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
         "../utils/set.rkt"
         "../utils/map.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "gen.rkt"
         "def-prim-runtime.rkt")

(begin-for-syntax
  (define/contract (gen-blm blm)
    (syntax? . -> . syntax?)
    #`(set (-ΓA #,(-Γ) #,blm))))

(define-syntax-parser def-const
  [(_ x:id)
   (define/with-syntax .x (prefix-id #'x))
   #'(begin
       (define .x (-b x))
       (hash-set-once! const-table 'x .x))])

(define-syntax (def-prim stx)
  (syntax-parse stx
    ;; Generate total predicates specially to reduce code duplicate
    [(_ o:id ((~literal ->) c:id ... (~literal boolean?)))
     #:when (for/and ([c (in-list (syntax->list #'(c ...)))])
              (free-identifier=? c #'any/c))
     (define n (length (syntax->list #'(c ...))))
     (define/with-syntax .o (prefix-id #'o))
     #`(begin
         (define .o ((total-pred #,n) 'o))
         (hash-set! prim-table 'o .o)
         (set-range! 'o 'boolean?)
         (update-arity! 'o #,n))]

    [(_ o:id sig:ff
        (~optional (~seq #:other-errors [cₑ:fc ...] ...)
                   #:defaults ([(cₑ 2) null]))
        (~optional (~seq #:refinements ref:ff ...)
                   #:defaults ([(ref 1) null]))
        (~optional (~seq #:lift-concrete? lift?:boolean)
                   #:defaults ([lift? #'#t])))
     
     (check-arity! stx)

     (define n (length (attribute sig.init)))
     (define arity (attribute sig.arity))
     (define/with-syntax .o (prefix-id #'o))
     (define/with-syntax defn-o
       (parameterize ([-o #'o]
                      [-⟪ℋ⟫ #'⟪ℋ⟫]
                      [-ℓ #'ℓ]
                      [-l #'l]
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
                      [-refs (syntax->list #'(ref ...))]
                      [-gen-blm gen-blm]
                      #;[-errs (syntax->list #'((cₑ ...) ...))])
         #`(define (.o #,(-⟪ℋ⟫) #,(-ℓ) #,(-l) #,(-Σ) #,(-Γ) #,(-Ws))
             #,@(gen-arity-check arity
                 (gen-precond-checks
                  (gen-ok-case))))))
     ;(pretty-write (syntax->datum #'defn-o))
     #`(begin
         (: .o : -⟦o⟧)
         defn-o
         (hash-set! prim-table 'o .o)
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o))
         (update-arity!
          'o
          #,(match arity
              [(arity-at-least n) #`(arity-at-least #,n)]
              [(? integer? n) n]))
         #,@(syntax-parse #|FIXME|# #'cₐ
              [(~or ((~literal and/c) d:id _ ...) d:id)
               (list #'(set-range! 'o 'd))]
              [_ '()]))]))

;; TODO remove code duplicate
(define-syntax (def-prim/custom stx)
  
  (define/contract (gen-defn o .o defn-o)
    (identifier? identifier? syntax?  . -> . syntax?)
    #`(begin
        (: #,.o : -⟦o⟧)
        #,defn-o
        (hash-set! prim-table '#,o #,.o)
        (hash-set! debug-table '#,o '#,(syntax->datum defn-o))))
  
  (syntax-parse stx
    [(_ (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id)
        #:domain ([W:id c:fc] ...)
        e:expr ...)
     (define n (length (syntax->list #'(c ...))))
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o
       #`(define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws)
           #,@(parameterize ([-o #'o]
                             [-⟪ℋ⟫ #'⟪ℋ⟫]
                             [-ℓ #'ℓ]
                             [-l #'l]
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
                             [-gen-blm gen-blm]
                             #;[-errs (syntax->list #'((cₑ ...) ...))])
                (gen-arity-check n
                 (gen-precond-checks
                  (syntax->list #'(e ...)))))))
     (gen-defn #'o #'.o defn-o)]
    [(_ (o:id ⟪ℋ⟫:id ℓ:id l:id Σ:id Γ:id Ws:id) e:expr ...)
     (define/with-syntax .o (prefix-id #'o))
     (define defn-o #'(define (.o ⟪ℋ⟫ ℓ l Σ Γ Ws) e ...))
     (gen-defn #'o #'.o defn-o)]))

(define-simple-macro (def-prim/todo x:id clauses ...)
  (def-prim/custom (x ⟪ℋ⟫ ℓ l Σ Γ Ws)
    (error 'x "TODO")))

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
   #'(hash-set-once! alias-table 'x 'y)])

(define-syntax-parser def-alias-internal
  [(_ x:id v:id)
   (define/with-syntax .x (prefix-id #'x))
   #'(begin
       (define .x v)
       (hash-set-once! alias-internal-table 'x v))])

(define-syntax-parser def-opq
  [(_ x:id c:fc)
   (define/with-syntax (r ...) (datum->syntax #f (rng->refinement #'c)))
   (define/with-syntax .x (prefix-id #'x))
   #'(begin
       (define x (-● (set r ...)))
       (hash-set-once! opq-table 'x x))])

(define-syntax-parser dec-implications
  [(_ [p:id (~literal ⇒) q:id ...] ...)
   (define clauses
     (append-map
      (λ (clause)
        (define/with-syntax (p ⇒ q ...) clause)
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
                 (foldr (λ (p* acc) (cons #`(add-exclusion! '#,p '#,p*) acc)) acc ps*))])))
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
