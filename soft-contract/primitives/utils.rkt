#lang racket/base

(provide (all-defined-out))

(require racket/base
         racket/match
         racket/list
         racket/syntax
         racket/contract
         racket/splicing
         syntax/parse
         syntax/parse/define
         (only-in "../utils/pretty.rkt" n-sub)
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (for-template racket/base
                       racket/contract
                       racket/syntax
                       syntax/parse
                       "../ast/definition.rkt"
                       "../runtime/main.rkt"))

(define-syntax-class hf
  #:description "restricted higher-order function contract"
  (pattern ((~literal ->) c:hc ... d:hc)))

(define-syntax-class hc
  #:description "restricted higher-order contract"
  (pattern _:hf)
  (pattern _:fc))

(define-syntax-class ff
  #:description "restricted first-order function contract"
  (pattern ((~literal ->) c:fc ... d:rngc)
           #:attr init (syntax->list #'(c ...))
           #:attr rest #f
           #:attr rng #'d
           #:attr arity (length (syntax->list #'(c ...))))
  (pattern ((~literal ->*) (c:fc ...) #:rest cᵣ:rstc d:rngc)
           #:attr init (syntax->list #'(c ...))
           #:attr rest #'cᵣ
           #:attr rng #'d
           #:attr arity (arity-at-least (length (syntax->list #'(c ...))))))

(define-syntax-class fc
  #:description "restricted flat contract"
  (pattern ((~or (~literal and/c) (~literal or/c)) _:fc _:fc _:fc ...))
  (pattern ((~literal not/c) _:fc))
  (pattern ((~literal cons/c) _:fc _:fc))
  (pattern ((~literal listof) _:fc))
  (pattern ((~literal list/c) _:fc ...))
  (pattern ((~or (~literal =/c)
                 (~literal >=/c) (~literal >/c)
                 (~literal <=/c) (~literal </c))
            _:real))
  (pattern _:lit)
  (pattern _:id))

(define-syntax-class rngc
  #:description "restricted function range"
  (pattern c:fc
           #:attr values (list #'c))
  (pattern ((~literal values) c₁:fc c₂:fc cᵣ:fc ...)
           #:attr values (syntax->list #'(c₁ c₂ cᵣ ...))))

(define-syntax-class rstc
  #:description "restricted rest args contract"
  (pattern (~literal list?))
  (pattern ((~literal listof) _:fc))
  #;(pattern ((~literal cons/c) _:fc _:rstc)))

(define-syntax-class lit
  #:description "restricted literals"
  (pattern x:number)
  (pattern x:symbol))

(define-syntax-class real
  #:description "literal real number"
  (pattern x #:when (real? (syntax-e #'x))))

(define-syntax-class symbol
  #:description "literal symbol"
  (pattern ((~literal quote) x) #:when (symbol? (syntax-e #'x))))

(define/contract (desugar-list/c cs)
  ((listof syntax?) . -> . syntax?)
  (foldr (λ (c acc) #`(cons/c #,c #,acc)) #'null? cs)) 

(define check-arity!
  (syntax-parser
    [(_ o:id ctc:ff
        (~optional (~seq #:other-errors [cₑ:fc ...] ...)
                   #:defaults ([(cₑ 2) null]))
        (~optional (~seq #:refinements ref:ff ...)
                   #:defaults ([(ref 1) null]))
        (~optional (~seq #:lift-concrete? lift?:boolean)
                   #:defaults ([lift? #'#t])))
     (define arity (attribute ctc.arity))
     (for ([refᵢ (in-list (syntax->list #'(ref ...)))])
       (define/syntax-parse ref:ff refᵢ)
       (unless (equal? arity (attribute ref.arity))
         (raise-syntax-error
          'def-prim
          (format "~a: all refinement clauses must have the same shape as the main contract for now" (syntax-e #'o))
          #'ref)))
     ;; TODO check arity in #:other-error clauses
     ]))

(define (prefix-id id [src id]) (format-id src ".~a" (syntax-e id)))

;; Convert contract range into list of refinement syntax
(define/contract (rng->refinement rng)
  (syntax? . -> . (listof syntax?))
  (syntax-parse rng
    [((~literal and/c) cᵢ ...)
     (append-map rng->refinement (syntax->list #'(cᵢ ...)))]
    [((~literal or/c) _ ...)
     (raise-syntax-error 'def-prim "or/c in #:refinement clause not supported" rng)]
    [((~literal not/c) d)
     (cond [(identifier? #'d) (list #'(-not/c 'd))]
           [else
            (raise-syntax-error 'def-prim "only identifier can follow not/c in refinement clause" rng)])]
    [((~literal cons/c) _ _)
     (raise-syntax-error
      'def-prim
      (format "~a: cons/c in range not suported for now" (syntax-e #'o))
      rng)]
    [((~literal =/c) x:number) (list #''real? #'(-=/c x))]
    [((~literal >/c) x:number) (list #''real? #'(->/c x))]
    [((~literal >=/c) x:number) (list #''real? #'(-≥/c x))]
    [((~literal </c) x:number) (list #''real? #'(-</c x))]
    [((~literal <=/c) x:number) (list #''real? #'(-≤/c x))]
    [x:lit (list #'(-≡/c (-b x)))]
    [(~literal any/c) '()]
    [(~literal none/c)
     (raise-syntax-error 'def-prim "refinement clause does not accept none/c in range" rng)]
    [c:id (list #''c)]))

;; Check if a predicate specifies a type that fits into the implementation's `Base` type
(define base-predicate?
  (syntax-parser
    [(~or (~literal integer?)
          (~literal rational?)
          (~literal real?)
          (~literal number?)
          (~literal zero?)
          (~literal inexact?)
          (~literal inexact-real?)
          (~literal exact-integer?)
          (~literal exact-positive-integer?)
          (~literal exact-nonnegative-integer?)
          (~literal exact-integer?)
          (~literal flonum?)
          (~literal single-flonum?)
          (~literal extflonum?)
          (~literal boolean?)
          (~literal path-string?)
          (~literal string?)
          (~literal symbol?)
          (~literal keyword?)
          (~literal char?)
          (~literal null?)
          (~literal void?)
          (~literal eof-object?)
          #;(~literal vector?)
          (~literal immutable?)
          (~literal positive?)
          (~literal negative?)
          (~literal zero?))
     #t]
    [_ #f]))

;; Check if value constrainted by contract definitly fits in the `Base` type in the implementation
(define range-is-base?
  (syntax-parser
    [((~literal and/c) c ...)
     (ormap range-is-base? (syntax->list #'(c ...)))]
    [((~literal or/c) c ...)
     (andmap range-is-base? (syntax->list #'(c ...)))]
    [((~literal not) _) #|conservative|# #f]
    [((~literal cons/c) _ _) #f]
    [((~or (~literal =/c)
           (~literal >/c) (~literal >=/c)
           (~literal </c) (~literal <=/c))
      _)
     #t]
    [x:lit #t]
    [x:id (base-predicate? #'x)]))

;; Fix slight mismatch with TR predicates
;; The mismatch doesn't make it wrong. It only limits cases where we can execute concretely
(define pred-for-TR
  (syntax-parser
    [(~literal integer?) #'exact-integer?]
    [p:id #'p]))

;; CLean up conditional clauses to make generated code a little more readable
(splicing-let ([tt? (syntax-parser [#t #t] [_ #f])]
               [ff? (syntax-parser [#f #t] [_ #f])])
  (define not*
    (syntax-parser
      [#t #'#f]
      [#f #'#t]
      ; ok if only care about truthiness, but be careful 1 ≠ (not (not 1))
      [((~literal not) x) #'x]
      [x #'(not x)]))
  
  (define/contract (and* es)
    ((listof syntax?) . -> . syntax?)
    (define cleaned-es
      (append-map (syntax-parser
                    [#t '()]
                    [((~literal and) e ...) (syntax->list #'(e ...))]
                    [e (list #'e)])
                  es))
    (match cleaned-es
      ['() #'#t]
      [(list e) e]
      [(list _ ... (? ff?) _ ...) #'#f]
      [_ #`(and #,@cleaned-es)]))

  (define/contract (or* es)
    ((listof syntax?) . -> . syntax?)
    (define cleaned-es
      (append-map (syntax-parser
                    [#f '()]
                    [((~literal or) e ...) (syntax->list #'(e ...))]
                    [e (list #'e)])
                  es))
    (match cleaned-es
      ['() #'#f]
      [(list e) e]
      [(list _ ... (? tt?) _ ...) #'#t]
      [else #`(or #,@cleaned-es)])))

(define/contract (gen-ids src prefix n)
  ((or/c #f syntax?) (or/c symbol? string?) integer? . -> . (listof identifier?))
  (for/list ([i (in-range n)])
    (format-id src "~a~a" prefix (n-sub i))))

(define/contract (new-thunk-table)
  (-> (values (hash/c symbol? (listof syntax?))
              (symbol? (or/c syntax? (listof syntax?)) . -> . symbol?)))
  (define m (make-hasheq))
  (values m
          (λ (f es)
            (hash-set! m f (if (syntax? es) (list es) es))
            f)))

(define (->id κ) (format-id #f "~a" κ))

(define-simple-macro (define-parameter/contract [x:id c v] ...)
  (begin (define/contract x (parameter/c c) (make-parameter v)) ...))
