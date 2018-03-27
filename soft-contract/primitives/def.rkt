#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     (only-in typed/racket/base index?)
                     racket/syntax
                     racket/match
                     racket/list
                     racket/contract
                     racket/function
                     racket/pretty
                     syntax/parse
                     syntax/parse/define
                     "def-utils.rkt"
                     (only-in "../utils/pretty.rkt" n-sub))
         racket/contract
         racket/match
         racket/set
         racket/splicing
         racket/promise
         syntax/parse/define
         set-extras
         "../utils/map.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "def-gen.rkt")

(define-syntax (def stx)

  (define (count-leaves c)
    (syntax-parse c
      [(~literal any/c) 0]
      [((~or (~literal and/c) (~literal or/c) (~literal not/c)) cᵢ ...)
       (apply + 0 (map count-leaves (syntax->list #'(cᵢ ...))))]
      [_ 1]))

  (syntax-parse stx
    ;; Generate total predicates specially to reduce code duplicate
    [(_ o:id ((~literal ->) c:id ... (~literal boolean?)))
     #:when (for/and ([c (in-list (syntax->list #'(c ...)))])
              (free-identifier=? c #'any/c))
     (define/with-syntax n (syntax-length #'(c ...)))
     (define/with-syntax .o (prefix-id #'o))
     (hack:make-available #'o make-total-pred prim-table set-range! update-arity! add-const!)
     #'(begin
         (define .o ((make-total-pred n) 'o))
         (hash-set! prim-table 'o .o)
         (set-range! 'o 'boolean?)
         (update-arity! 'o n)
         (add-const! #'o 'o))]
    [(_ o:id sig:hc
        (~optional (~seq #:refinements ref:ff ...)
                   #:defaults ([(ref 1) null]))
        (~optional (~seq #:volatile? volatile?:boolean)
                   #:defaults ([volatile? #'#t]))
        (~optional (~seq #:lift-concrete? lift?:boolean)
                   #:defaults ([lift? #'#t])))

     (check-shape-ok #'o #'sig (syntax->list #'(ref ...)))
     (define/with-syntax .o (prefix-id #'o))
     (define/with-syntax stx-arity
       (let go ([arity (normalize-arity (attribute sig.arity))])
         (match arity
           [(? number? n) n]
           [(arity-at-least n) #`(arity-at-least #,n)]
           [(? list? l) #`(list #,@(map go l))])))
     (define max-inits
       (let go ([c #'sig])
         (syntax-parse c
           [((~literal ->) c ... _) (syntax-length #'(c ...))]
           [((~literal ->*) (c ...) #:rest _ _) (syntax-length #'(c ...))]
           [((~literal case->) clauses ...)
            (apply max 0 (map
                          (syntax-parser
                            [((~literal ->) c ... #:rest _ _) (syntax-length #'(c ...))]
                            [((~literal ->) c ... _) (syntax-length #'(c ...))])
                          (syntax->list #'(clauses ...))))]
           [((~literal ∀/c) _ c) (go #'c)])))
     (define/with-syntax defn-o
       #`(define (.o W ℓ Φ^ Ξ Σ)
           #,@(parameterize ([-o #'o]
                             [-ℓ #'ℓ]
                             [-W #'W]
                             [-Φ^ #'Φ^]
                             [-Ξ #'Ξ]
                             [-Σ #'Σ]
                             [-sig #'sig]
                             [-Vⁿ (gen-ids #'W 'V max-inits)]
                             [-Vᵣ (format-id #'W "Vᵣ")]
                             [-gen-lift? (syntax-e #'lift?)]
                             [-refinements (syntax->list #'(ref ...))]
                             [-volatile? (syntax-e #'volatile?)])
                (gen-cases))))
     (define/contract maybe-set-partial (listof syntax?)
       (let go ([sig #'sig])
         (hack:make-available #'o set-partial!)
         (syntax-parse sig
           [(dom ... . (~literal ->) . _)
            (define n (apply + 0 (map count-leaves (syntax->list #'(dom ...)))))
            (list #`(set-partial! 'o #,n))]
           [((inits ...) #:rest rest . (~literal ->*) . _)
            (define n
              (+ (apply + 0 (map count-leaves (syntax->list #'(inits ...))))
                 (count-leaves #'rest)))
            (list #`(set-partial! 'o #,n))]
           [((~literal case->) clause _ ...)
            (syntax-parse #'clause ; sloppily count first clause only
              [((~literal ->) c ... #:rest r _)
               (define n
                 (+ (apply + 0 (count-leaves (syntax->list #'(c ...))))
                    (count-leaves #'r)))
               
               (list #`(set-partial! 'o #,n))]
              [((~literal ->) c ... _)
               (define n (apply + 0 (map count-leaves (syntax->list #'(c ...)))))
               (list #`(set-partial! 'o #,n))])]
           [((~literal ∀/c) c) (go #'c)]
           [_ '()])))
     (hack:make-available #'o prim-table debug-table set-range! update-arity! add-const!)
     #`(begin
         (: .o : ⟦F⟧^)
         defn-o
         (add-const! #'o 'o)
         (hash-set! prim-table 'o .o)
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o))
         (update-arity! 'o stx-arity)
         #,@maybe-set-partial
         #,@(syntax-parse #'sig
              [((~literal ->) _ ... (~or d:id ((~literal and/c) d:id _ ...)))
               (list #'(set-range! 'o 'd))]
              [((~literal ->*) _ ... (~or d:id ((~literal and/c) d:id _ ...)))
               (list #'(set-range! 'o 'd))]
              [_ '()]))]

    ;; Hack mode
    [(_ (o:id W:id ℓ:id Φ^:id Ξ:id Σ:id)
        #:init ([V:id (~and c (~or _:id ((~literal and/c) _:id ...)))] ...)
        (~optional (~seq #:rest [Vᵣ:id cᵣ])
                   #:defaults ([cᵣ #'null?]
                               [Vᵣ #'dummy]))
        e ...)
     (define/with-syntax ok-pat
       (syntax-parse #'cᵣ
         [(~literal null?) #'(list V ...)]
         [((~literal listof) _:id) #'(list* V ... Vᵣ)]
         [_
          (raise-syntax-error
           (syntax-e #'o) "unsupported rest contract in hack mode" #'cᵣ)]))
     (define arity
       (syntax-parse #'cᵣ
         [(~literal null?) (syntax-length #'(c ...))]
         [_ (arity-at-least (syntax-length #'(c ...)))]))
     (define/with-syntax stx-arity
       (match arity
         [(? number? n) n]
         [(arity-at-least n) #`(arity-at-least #,n)]))
     (define/with-syntax .o (prefix-id #'o))
     (define ?c-elem
       (syntax-parse #'cᵣ
         [((~literal listof) c) #'c]
         [_ #f]))
     (define/with-syntax defn-o
       #`(define (.o W ℓ Φ^ Ξ Σ)
           #,(parameterize ([-o #'o]
                            [-ℓ #'ℓ]
                            [-W #'W]
                            [-Φ^ #'Φ^]
                            [-Ξ #'Ξ]
                            [-Σ #'Σ]
                            [-Vⁿ (syntax->list #'(V ...))]
                            [-Vᵣ #'Vᵣ])
               (syntax-parse #'(V ...)
                 [()
                  (list*
                   #`(let ([Vᵣ W])
                       #,@(gen-flat-checks '()
                                           ?c-elem
                                           (syntax->list #'(e ...)))))]
                 [_
                  (hack:make-available #'o r:blm)
                  #`(match W
                      [ok-pat
                       #,@(gen-flat-checks (syntax->list #'(c ...))
                                           ?c-elem
                                           (syntax->list #'(e ...)))]
                      [_
                       (define msg '(#,(string->symbol (format "~v" arity))))
                       (r:blm ℓ 'o msg W)])]))))
     (hack:make-available #'o prim-table debug-table set-range! update-arity! add-const! set-partial!)
     (define/contract maybe-set-partial (listof syntax?)
       (let ([n
              (+ (apply + (map count-leaves (syntax->list #'(c ...))))
                 (syntax-parse #'cᵣ
                   [(~literal null?) 0]
                   [((~literal listof) c) (+ 1 (count-leaves #'c))]))])
         (list #`(set-partial! 'o #,n))))
     #`(begin
         (: .o : ⟦F⟧^)
         defn-o
         (add-const! #'o 'o)
         (hash-set! prim-table 'o .o)
         (hash-set! debug-table 'o '#,(syntax->datum #'defn-o))
         (update-arity! 'o stx-arity)
         #,@maybe-set-partial)]
    ))

(define-simple-macro (def* (o:id ...) clauses ...)
  (begin (def o clauses ...) ...))

(define-simple-macro
  (def-pred p:id (~optional (dom:fc ...) #:defaults ([(dom 1) (list #'any/c)])))
  (def p (dom ... . -> . boolean?)))

(define-simple-macro (def-preds (p:id ...) rst ...)
  (begin
    (def-pred p rst ...) ...))

(define-syntax-parser def-alias
  [(_ x:id y:id)
   (hack:make-available #'x add-alias!)
   #'(add-alias! #'x #'y)])

(define-syntax-parser def-alias-internal
  [(_ x:id v:id)
   (hack:make-available #'x add-const!)
   #'(add-const! #'x v)])

(define-syntax-parser def-opq
  [(_ x:id c:fc)
   (define/with-syntax (r ...) (datum->syntax #f (range->refinement #'c)))
   (hack:make-available #'x opq-table)
   #'(hash-set-once! opq-table 'x (-● (set r ...)))])

(define-syntax-parser def-const
  [(_ x:id)
   (hack:make-available #'x add-const!)
   #'(add-const! #'x (-b x))])

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

(define-syntax-parser def-struct
  [(_ s:id ([f:id c:c] ...)
      (~optional (~seq #:extra-constructor-name mk-s:id ...)
                 #:defaults ([(mk-s 1) '()]))
      (~optional (~seq #:substructs (_ s*:id s*-args ...) ...)
                 #:defaults ([(s* 1) '()]
                             [(s*-args 2) '()]))
      (~optional (~seq #:parent-fields (c₀:id ...))
                 #:defaults ([(c₀ 1) '()])))
   (define/with-syntax s? (format-id #'s "~a?" (syntax-e #'s) #:source #'s))
   (define/with-syntax (s-f ...) (for/list ([f (in-list (syntax->list #'(f ...)))])
                                   (format-id #'s "~a-~a" (syntax-e #'s) (syntax-e f))))
   (define/with-syntax (impl-dec ...)
     (with-syntax ([(s*? ...)
                    (map
                     (syntax-parser
                       [s (format-id #'s "~a?" (syntax-e #'s) #:source #'s)])
                     (syntax->list #'(s* ...)))])
       (cond [(null? (syntax->list #'(s*? ...))) '()]
             [else (list #`(dec-implications [s*? ⇒ s?] ...))])))
   #`(begin
       (def-pred s?)
       (def s (c₀ ... c ... . -> . s?))
       (def-alias mk-s s) ...
       (def s-f (s? . -> . c)) ...
       impl-dec ...
       (def-struct s* s*-args ... #:parent-fields (c₀ ... c ...)) ...)])
