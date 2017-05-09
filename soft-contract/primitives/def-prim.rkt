#lang typed/racket/base

;; This module implements facitilies for defining primitive constants and 1st-order functions
;; TODO:
;; - [ ] listof
;; - [ ] multiple valued return
;; - [ ] #:other-errors
;; - [ ] limited dependent contract to specify `vector-ref`
;;      , or actually just def/custom it if there are only few cases
(provide (all-defined-out))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/pretty
                     syntax/parse
                     syntax/parse/define
                     "utils.rkt"
                     (only-in "../utils/pretty.rkt" n-sub))
         racket/contract
         racket/match
         racket/set
         racket/splicing
         racket/promise
         syntax/parse/define
         set-extras
         "../utils/map.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "gen.rkt")

(begin-for-syntax
  (define/contract (gen-blm.prim blm)
    (syntax? . -> . syntax?)
    #`(set (-ΓA (-Γ-facts #,(-Γ)) #,blm)))
  (define/contract (gen-blm.ext blm)
    (syntax? . -> . syntax?)
    #`(#,(-⟦k⟧) #,blm #,(-$) #,(-Γ) #,(-⟪ℋ⟫) #,(-Σ)))
  )

(define-syntax-parser def-const
  [(_ x:id)
   (hack:make-available #'x const-table)
   #'(hash-set-once! const-table 'x (-b x))])

(define-syntax (def-prim stx)
  
  (syntax-parse stx
    ;; Generate total predicates specially to reduce code duplicate
    [(_ o:id ((~literal ->) c:id ... (~literal boolean?)))
     #:when (for/and ([c (in-list (syntax->list #'(c ...)))])
              (free-identifier=? c #'any/c))
     (define/with-syntax n (length (syntax->list #'(c ...))))
     (define/with-syntax .o (prefix-id #'o))
     (hack:make-available #'o make-total-pred prim-table set-range! update-arity!)
     
     #'(begin
         (define .o ((make-total-pred n) 'o))
         (hash-set! prim-table 'o (-⟦o⟧.boxed .o))
         (set-range! 'o 'boolean?)
         (update-arity! 'o n))]

    [(_ o:id sig:ff
        (~optional (~seq #:other-errors [cₑ:fc ...] ...)
                   #:defaults ([(cₑ 2) null]))
        (~optional (~seq #:refinements ref:ff ...)
                   #:defaults ([(ref 1) null]))
        (~optional (~seq #:volatile? volatile?:boolean)
                   #:defaults ([volatile? #'#f]))
        ;; TODO: how to default `lift?` to `(not (volatile?))`
        (~optional (~seq #:lift-concrete? lift?:boolean)
                   #:defaults ([lift? #'#t])))
     
     (check-arity! stx)

     (define n (length (attribute sig.init)))
     (define arity (attribute sig.arity))
     (define/with-syntax .o (prefix-id #'o))
     (define/with-syntax defn-o
       (parameterize ([-o #'o]
                      [-⟪ℋ⟫ #'⟪ℋ⟫]
                      [-ℒ #'ℒ]
                      [-Σ #'Σ]
                      [-σ #'σ]
                      [-M #'M]
                      [-Γ #'Γ]
                      [-Ws #'Ws]
                      [-Wₙ (gen-ids #'W 'W n)]
                      [-sₙ (gen-ids #'s 's n)]
                      [-bₙ (gen-ids #'b 'b n)]
                      [-W* (format-id #'W* "W*")]
                      [-b* (format-id #'b* "b*")]
                      [-s* (format-id #'s* "s*")]
                      [-sig #'sig]
                      [-lift? (syntax-e #'lift?)]
                      [-volatile? (syntax-e #'volatile?)]
                      [-refs (syntax->list #'(ref ...))]
                      [-gen-blm gen-blm.prim]
                      #;[-errs (syntax->list #'((cₑ ...) ...))])
         #`(define (.o #,(-⟪ℋ⟫) #,(-ℒ) #,(-Σ) #,(-Γ) #,(-Ws))
             #,@(gen-arity-check arity
                 (gen-precond-checks
                  (gen-ok-case))))))
     #;(pretty-write (syntax->datum #'defn-o))
     (define/contract maybe-set-partial (listof syntax?)
       (let ()
         (define (count-leaves c)
           (syntax-parse c
             [(~literal any/c) 0]
             [((~or (~literal and/c) (~literal or/c) (~literal not/c)) cᵢ ...)
              (apply + 0 (map count-leaves (syntax->list #'(cᵢ ...))))]
             [_ 1]))
         
         (syntax-parse #'sig
           [(dom ... . (~literal ->) . _)
            (define n (apply + 0 (map count-leaves (syntax->list #'(dom ...)))))
            (hack:make-available #'o set-partial!)
            (list #`(set-partial! 'o #,n))]
           [((inits ...) #:rest rest . (~literal ->*) . _)
            (define n
              (+ (apply + 0 (map count-leaves (syntax->list #'(inits ...))))
                 (count-leaves #'rest)))
            (hack:make-available #'o set-partial!)
            (list #`(set-partial! 'o #,n))]
           [_ '()])))

     (hack:make-available #'o prim-table debug-table set-range! update-arity!)

     #`(begin
         (: .o : -⟦o⟧)
         defn-o
         (hash-set! prim-table 'o (-⟦o⟧.boxed .o))
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o))
         (update-arity!
          'o
          #,(match arity
              [(arity-at-least n) #`(arity-at-least #,n)]
              [(? integer? n) n]))
         #,@maybe-set-partial
         #,@(syntax-parse #|FIXME|# #'cₐ
              [(~or ((~literal and/c) d:id _ ...) d:id)
               (list #'(set-range! 'o 'd))]
              [_ '()]))]))

;; TODO remove code duplicate
(define-syntax (def-prim/custom stx)

  (define/contract (gen-defn o .o defn-o)
    (identifier? identifier? syntax?  . -> . syntax?)
    (hack:make-available o prim-table debug-table)
    #`(begin
        (: #,.o : -⟦o⟧)
        #,defn-o
        (hash-set! prim-table '#,o (-⟦o⟧.boxed #,.o))
        (hash-set! debug-table '#,o '#,(syntax->datum defn-o))))
  
  (syntax-parse stx
    [(_ (o:id ⟪ℋ⟫:id ℒ:id Σ:id Γ:id Ws:id)
        #:domain ([W:id c:fc] ...)
        e:expr ...)
     (define n (length (syntax->list #'(c ...))))
     (define/with-syntax .o (prefix-id #'o))
     (hack:make-available #'o update-arity!)
     (define defn-o
       #`(begin
           (define (.o ⟪ℋ⟫ ℒ Σ Γ Ws)
             #,@(parameterize ([-o #'o]
                               [-⟪ℋ⟫ #'⟪ℋ⟫]
                               [-ℒ #'ℒ]
                               [-Σ #'Σ]
                               [-σ #'σ]
                               [-M #'M]
                               [-Γ #'Γ]
                               [-Ws #'Ws]
                               [-Wₙ (syntax->list #'(W ...))]
                               [-sₙ (gen-ids #'s 's n)]
                               [-bₙ (gen-ids #'b 'b n)]
                               [-W* (format-id #'W* "W*")]
                               [-b* (format-id #'b* "b*")]
                               [-s* (format-id #'s* "s*")]
                               [-sig #'(-> c ... any/c)]
                               [-gen-blm gen-blm.prim]
                               #;[-errs (syntax->list #'((cₑ ...) ...))])
                  (gen-arity-check n
                                   (gen-precond-checks
                                    (syntax->list #'(e ...))))))
           (update-arity! 'o #,n)))
     (gen-defn #'o #'.o defn-o)]
    [(_ (o:id ⟪ℋ⟫:id ℒ:id Σ:id Γ:id Ws:id) e:expr ...)
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o #'(define (.o ⟪ℋ⟫ ℒ Σ Γ Ws) e ...))
     (gen-defn #'o #'.o defn-o)]))

(define-simple-macro (def-prim/todo x:id clauses ...)
  (def-prim/custom (x ⟪ℋ⟫ ℒ Σ Γ Ws)
    (error 'def-prim "TODO: ~a" 'x)))

(define-simple-macro (def-prims (o:id ... (~optional (~seq #:todo o*:id ...)
                                                     #:defaults ([(o* 1) '()])))
                       clauses ...)
  (begin
    (def-prim o clauses ...) ...
    (def-prim/todo o* clauses ...) ...))

(define-simple-macro (def-pred p:id (~optional (dom:fc ...)
                                               #:defaults ([(dom 1) (list #'any/c)])))
  (def-prim p (dom ... . -> . boolean?)))

(define-simple-macro (def-preds (p:id ... (~optional (~seq #:todo q:id ...)
                                                     #:defaults ([(q 1) '()])))
                       rst ...)
  (begin
    (def-pred p rst ...) ...
    (def-pred/todo q rst ...) ...))

(define-simple-macro (def-pred/todo p:id (~optional (dom:fc ...)
                                                    #:defaults ([(dom 1) (list #'any/c)])) ...)
  (def-prim/todo p (dom ... . -> . boolean?)))

(define-syntax-parser def-alias
  [(_ x:id y:id)
   (hack:make-available #'x alias-table)
   #'(hash-set-once! alias-table 'x 'y)])

(define-syntax-parser def-alias-internal
  [(_ x:id v:id)
   (hack:make-available #'x const-table)
   #'(hash-set-once! const-table 'x v)])

(define-syntax-parser def-opq
  [(_ x:id c:fc)
   (define/with-syntax (r ...) (datum->syntax #f (rng->refinement #'c)))
   (hack:make-available #'x opq-table)
   #'(hash-set-once! opq-table 'x (-● (set r ...)))])

(define-syntax-parser dec-implications
  [(_ [p:id (~literal ⇒) q:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (define/with-syntax (p ⇒ q ...) clause)
        (define/with-syntax add-implication! (format-id #'p "add-implication!"))
        (for/list ([q (in-list (syntax->list #'(q ...)))])
          #`(add-implication! 'p '#,q)))
      (syntax->list #'([p ⇒ q ...] ...))))
   #`(begin #,@clauses)])

(define-syntax-parser dec-exclusions
  [(_ [p:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (define ps (syntax->list clause))
        (let go ([ps ps] [acc '()])
          (match ps
            [(list) acc]
            [(cons p ps*)
             (go ps*
                 (foldr (λ (p* acc)
                          (define/with-syntax add-exclusion! (format-id p "add-exclusion!"))
                          (cons #`(add-exclusion! '#,p '#,p*) acc))
                        acc
                        ps*))])))
      (syntax->list #'([p ...] ...))))
   #`(begin #,@clauses)])

(define-syntax-parser dec-partitions
  [(_ [p:id (q:id ...)] ...)
   (define impl-clauses
     (append-map
      (λ (clause)
        (define/with-syntax (p (q ...)) clause)
        (for/list ([q (in-list (syntax->list #'(q ...)))])
          #`(dec-implications [#,q ⇒ p])))
      (syntax->list #'([p (q ...)] ...))))
   #`(begin
       (dec-exclusions (q ...) ...)
       #,@impl-clauses)])

(define-syntax (def-ext stx)
  (define/contract (gen-defn o .o defn)
    (identifier? identifier? syntax? . -> . syntax?)
    (hack:make-available o prim-table debug-table)
    #`(begin
        (: #,.o : -⟦f⟧)
        #,defn
        (hash-set! prim-table '#,o (-⟦f⟧.boxed #,.o))
        (hash-set! debug-table '#,o '#,(syntax->datum defn))))
  
  (syntax-parse stx
    
    ;; Only declare contract, providing crudest approximation
    [(_ o:id c:hf)
     (define/syntax-parse (cₓ ...) (attribute c.init))
     (define/syntax-parse d (attribute c.rng))
     (define/with-syntax (W ...) (gen-ids #'o 'W (length (syntax->list #'(cₓ ...)))))
     (hack:make-available #'o add-leak! bgn0.e∷ σₖ⊕!)
     #`(def-ext (o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
         #:domain ([W cₓ] ...)
         (match-define (-Σ σ σₖ _) Σ)
         (define sₐ (?t@ 'o (-W¹-t W) ...))
         (define Wₐ (-W (list #,(parameterize ([-o #'o]
                                               [-σ #'σ])
                                  (gen-wrap #'d #'-●.V #'sₐ)))
                        sₐ))
         (begin (add-leak! Σ (-W¹-V W)) ...)
         (define αₖ (-ℋ𝒱))
         (define κ (-κ (bgn0.e∷ Wₐ '() ⊥ρ ⟦k⟧) Γ ⟪ℋ⟫ '()))
         (σₖ⊕! Σ αₖ κ)
         {set (-ς↑ αₖ Γ ⟪ℋ⟫)})]

    ;; Declaring simple result, skipping havoc-ing of arguments
    [(_ (o:id $:id ℒ:id Ws:id Γ:id ⟪ℋ⟫:id Σ:id ⟦k⟧:id)
        #:domain ([W:id c:hc] ...)
        #:result e)
     #'(def-ext (o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
         #:domain ([W c] ...)
         (define sₐ (apply ?t@ 'o (map -W¹-t Ws)))
         (⟦k⟧ (-W e sₐ) $ Γ ⟪ℋ⟫ Σ))]

    ;; Custom modes for hacking
    [(_ (o:id $:id ℒ:id Ws:id Γ:id ⟪ℋ⟫:id Σ:id ⟦k⟧:id)
        #:domain ([W:id c:hc] ...)
        e:expr ...)
     (define n (length (syntax->list #'(W ...))))
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o
       #`(define (.o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
           (define ℓ (-ℒ-app ℒ))
           #,@(parameterize ([-o #'o]
                             [-⟪ℋ⟫ #'⟪ℋ⟫]
                             [-ℒ #'ℒ]
                             [-ℓ #'ℓ]
                             [-Σ #'Σ]
                             [-σ #'σ]
                             [-M #'M]
                             [-Γ #'Γ]
                             [-⟦k⟧ #'⟦k⟧]
                             [-$ #'$]
                             [-Ws #'Ws]
                             [-Wₙ (syntax->list #'(W ...))]
                             [-sₙ (gen-ids #'s 's n)]
                             [-bₙ (gen-ids #'b 'b n)]
                             [-W* (format-id #'W* "W*")]
                             [-b* (format-id #'b* "b*")]
                             [-s* (format-id #'s* "s*")]
                             [-sig #'(-> c ... any/c)]
                             [-gen-blm gen-blm.ext])
                (gen-arity-check n
                                 (gen-precond-checks
                                  (gen-arg-wraps
                                   (syntax->list #'(e ...))))))))
     #;(pretty-write (syntax->datum defn-o))
     (gen-defn #'o #'.o defn-o)]
    
    ;; Skipping precondition checks
    [(_ (o:id $:id ℒ:id Ws:id Γ:id ⟪ℋ⟫:id Σ:id ⟦k⟧:id) e:expr ...)
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o #`(define (.o $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) e ...))
     (gen-defn #'o #'.o defn-o)]))
