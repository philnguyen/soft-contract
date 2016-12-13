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

(define-syntax-class sig
  #:description "restricted function signature"
  (pattern ((~literal ->) _:fc ... _:rngc))
  (pattern ((~literal ->*) (_:fc ...) #:rest _:rstc _:rngc)))

(define-syntax-class fc
  #:description "restricted first-order contract"
  (pattern ((~or (~literal and/c) (~literal or/c)) _:fc _:fc _:fc ...))
  (pattern ((~literal not/c) _:fc))
  (pattern ((~literal cons/c) _:fc _:fc))
  (pattern ((~literal listof) _:fc))
  (pattern ((~or (~literal =/c)
                 (~literal >=/c) (~literal >/c)
                 (~literal <=/c) (~literal </c))
            _:real))
  (pattern _:lit)
  (pattern _:id))

(define-syntax-class rngc
  #:description "restricted function range"
  (pattern _:fc)
  (pattern ((~literal values) _:fc _:fc _:fc ...)))

(define-syntax-class rstc
  #:description "restricted rest args contract"
  (pattern (~literal list?))
  (pattern ((~literal listof) _:fc))
  (pattern ((~literal cons/c) _:fc _:rstc)))

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

(define check-arity!
  (syntax-parser
    [(_ o:id ((~literal ->) cₓ:fc ... cₐ:fc)
        #:other-errors [cₑ:fc ...] ...
        #:refinements [(~literal ->) rₓ:fc ... rₐ:fc] ...
        #:lift-concrete? _)
     (define n (length (syntax->list #'(cₓ ...))))
     (define (check-domain-arity! doms)
       (define m (length (syntax->list doms)))
       (unless (equal? n m)
         (raise-syntax-error
          'def-prim
          (format "~a has arity ~a, but get ~a" (syntax-e #'o) n m)
          doms)))
     (for-each check-domain-arity! (syntax->list #'((cₑ ...) ...)))
     (for-each check-domain-arity! (syntax->list #'((rₓ ...) ...)))]
    [_ (void)]))

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

;; Specify primitives that shouldn't be lifted
(define skip-base-case-lifting?
  (syntax-parser
    ;; These won't type check.
    ;; The untyped version takes `any/c`, but the typed ones take `Set`
    [(~or (~literal set-equal?)
          (~literal set-eq?)
          (~literal set-eqv?))
     #t]
    [_ #f]))

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

(define/contract (new-thunk-table)
  (-> (values (hash/c symbol? (listof syntax?))
              (symbol? (or/c syntax? (listof syntax?)) . -> . symbol?)))
  (define m (make-hasheq))
  (values m
          (λ (f es)
            (hash-set! m f (if (syntax? es) (list es) es))
            f)))

(define/contract (gen-ids src prefix n)
  ((or/c #f syntax?) (or/c symbol? string?) integer? . -> . (listof identifier?))
  (for/list ([i (in-range n)])
    (format-id src "~a~a" prefix (n-sub i))))
