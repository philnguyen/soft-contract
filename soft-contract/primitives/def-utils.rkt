#lang racket/base

(provide (all-defined-out))

(require racket/base
         racket/match
         racket/bool
         racket/list
         racket/set
         racket/syntax
         racket/contract
         racket/function
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
                       "../ast/signatures.rkt"
                       "../runtime/signatures.rkt"))

(define-syntax-class c
  #:description "restricted contract"
  (pattern _:fc)
  (pattern _:hc)
  (pattern _:mc))

(define-syntax-class d
  #:description "restricted contract range"
  #:attributes (values)
  (pattern c:c                                    #:attr values (list #'c))
  (pattern ((~literal values) d₁:c d₂:c d*:c ...) #:attr values (list* #'d₁ #'d₂ (syntax->list #'(d* ...))))
  (pattern (~literal any)                         #:attr values #f))

(define-syntax-class hc
  #:description "restricted higher-order-contract"
  #:attributes (arity)
  (pattern c:poly-hc #:attr arity (attribute c.arity))
  (pattern c:mono-hc #:attr arity (attribute c.arity)))

(define-syntax-class poly-hc
  #:description "restricted polymorphic function contract"
  (pattern ((~literal ∀/c) (_:id ...) c:mono-hc)
           #:attr arity (attribute c.arity)))

(define-syntax-class mono-hc
  #:description "restricted monomorphic function contract"
  #:attributes (arity)
  (pattern ((~literal ->) c:c ... _:d)
           #:attr arity (syntax-length #'(c ...)))
  (pattern ((~literal ->*) (c:c ...) #:rest _:c _:d)
           #:attr arity (arity-at-least (syntax-length #'(c ...))))
  (pattern ((~literal case->) c:case-clause ...)
           #:attr arity (normalize-arity
                         (for/list ([c (in-syntax-list #'(c ...))]) ; TODO more concise?
                           (syntax-parse c
                             [c:case-clause (attribute c.arity)])))))

(define-syntax-class case-clause
  #:description "restricted case-> clause"
  #:attributes (arity)
  (pattern [(~literal ->) c:c ... _:d]
           #:attr arity (syntax-length #'(c ...)))
  (pattern [(~literal ->) c:c ... #:rest _:c _:d]
           #:attr arity (arity-at-least (syntax-length #'(c ...)))))

(define-syntax-class fc
  #:description "restricted first-order contract"
  (pattern (~and x:id (~not (~literal any)))) ; only used for seals
  (pattern _:o)
  (pattern _:lit)
  (pattern ((~literal not/c) _:fc))
  (pattern (_:cmp r:number) #:when (real? (syntax-e #'r))))

(define-syntax-class cmp
  #:description "number range contract combinator"
  (pattern (~or (~literal >/c)
                (~literal </c)
                (~literal =/c)
                (~literal >=/c)
                (~literal <=/c))))

(define-syntax-class mc
  #:description "restricted ambig-order contract"
  ;; FIXME not really. Vector and other mutable stuff always higher-order
  (pattern ((~literal and/c) _:c ...))
  (pattern ((~literal or/c) _:c ...))
  (pattern ((~literal cons/c) _:c _:c))
  (pattern ((~literal listof) _:c))
  (pattern ((~literal list/c) _:c ...))
  (pattern ((~literal vectorof) _:c))
  (pattern ((~literal vector/c) _:c ...))
  (pattern ((~literal set/c) _:c))
  (pattern ((~literal hash/c) _:c _:c)))

(define-syntax-class rc
  #:description "restricted contract on rest args"
  (pattern ((~literal listof) _:fc)))

(define-syntax-class lit
  #:description "restricted literal"
  (pattern _:number)
  (pattern _:boolean)
  (pattern ((~literal quote) x) #:when (symbol? (syntax-e #'x))))

(define-syntax-class o
  #:description "restricted base predicates"
  (pattern (~or (~literal any/c)
                (~literal none/c)
                (~literal integer?)
                (~literal rational?)
                (~literal real?)
                (~literal number?)
                (~literal positive?)
                (~literal negative?)
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
                (~literal immutable?)
                (~literal list?))))

(define-syntax-class ff
  #:description "restricted first-order function contracts"
  (pattern ((~literal ->) _:fc ... _:fd))
  (pattern ((~literal ->*) (_:fc ...) #:rest _:rc _:fd)))

(define-syntax-class fd
  #:description "restricted first-order function range"
  (pattern _:fc)
  (pattern ((~literal values) _:fc _:fc _:fc ...)))

(define base?
  ;; Ones that fit in implementation's `Base`
  (syntax-parser
    [(~or (~literal integer?)
          (~literal rational?)
          (~literal real?)
          (~literal number?)
          (~literal positive?)
          (~literal negative?)
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
          (~literal immutable?))
     #t]
    [_ #f]))

(define c-flat?
  (syntax-parser
    [_:fc #t]
    [((~or (~literal and/c)
           (~literal or/c)
           (~literal list/c)
           (~literal listof)
           (~literal cons/c))
      c ...)
     (andmap c-flat? (syntax->list #'(c ...)))]
    [_ #f]))

(define/contract in-syntax-list (syntax? . -> . sequence?) (compose in-list syntax->list))

(define/contract (check-shape-ok o sig sigs)
  (identifier? syntax? (listof syntax?) . -> . any)
  (define sig-shape
    (syntax-parser
      [((~literal ->) dom ... rng:d)
       (values (length (syntax->list #'(dom ...))) (length (attribute rng.values)))]
      [((~literal ->*) (dom ...) #:rest _ rng:d)
       (values (arity-at-least (length (syntax->list #'(dom ...))))
               (length (attribute rng.values)))]
      [((~literal ∀/c) c) (sig-shape #'c)]
      [_
       ;; TODO generalize checks for case->
       (values #f #f)]))
  (define-values (num-args num-rng) (sig-shape sig))
  (when (and num-args num-rng)
    (for ([sigᵢ (in-list sigs)])
      (define-values (num-argsᵢ num-rngᵢ) (sig-shape sigᵢ))
      (unless (and (arity-compatible? num-args num-argsᵢ)
                   (arity-compatible? num-rng num-rngᵢ))
        (raise-syntax-error (syntax-e #'o) "incompatible shape" sig (list sigᵢ))))))

(define-simple-macro (define-parameter/contract [x:id c v] ...)
  (begin (define/contract x (parameter/c c) (make-parameter v)) ...))

(define/contract (gen-ids src prefix n)
  ((or/c #f syntax?) (or/c symbol? string?) integer? . -> . (listof identifier?))
  (for/list ([i (in-range n)])
    (format-id src "~a~a" prefix (n-sub i))))

(define (syntax-length stx) (length (syntax->list stx)))

(define/contract (arity-compatible? a b)
  ((or/c #f procedure-arity?) (or/c #f procedure-arity?) . -> . boolean?)
  ((and a b) . implies . (or (arity-includes? a b) (arity-includes? b a))))
