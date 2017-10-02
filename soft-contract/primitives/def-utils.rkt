#lang racket/base

(provide (all-defined-out))

(require racket/base
         racket/match
         racket/bool
         racket/list
         racket/set
         racket/extflonum
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
                       racket/string
                       racket/flonum
                       racket/extflonum
                       racket/fixnum
                       racket/stream
                       racket/contract
                       racket/generator
                       racket/dict
                       racket/set
                       (prefix-in z: compiler/decompile)
                       (prefix-in z: compiler/zo-parse)
                       (prefix-in z: compiler/zo-marshal)
                       (prefix-in z: compiler/zo-structs)
                       (only-in racket/function normalized-arity?)
                       racket/contract
                       racket/syntax
                       syntax/parse
                       math/base
                       "../ast/signatures.rkt"
                       "../runtime/signatures.rkt"))

(define-syntax-class c
  #:description "restricted contract"
  (pattern (~and _:id (~not (~literal any)))) ; only used for seals
  (pattern _:fc)
  (pattern _:hc)
  (pattern _:mc))

(define-syntax-class d
  #:description "restricted contract range"
  #:attributes (values)
  (pattern c:c                                    #:attr values (list #'c))
  (pattern ((~literal values) d₁:c d₂:c d*:c ...) #:attr values (list* #'d₁ #'d₂ (syntax->list #'(d* ...))))
  (pattern (~literal any)                         #:attr values 'any))

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
  (pattern ((~literal listof) _:fc))
  (pattern (~literal list?)))

(define-syntax-class lit
  #:description "restricted literal"
  (pattern _:number)
  (pattern _:boolean)
  (pattern ((~literal quote) x) #:when (symbol? (syntax-e #'x))))

(define-syntax-class o
  #:description "restricted base predicates"
  ;; TODO This was initially intended to prevent typos. But it's become unwieldy.
  (pattern (~or (~literal any/c)
                (~literal none/c)
                (~literal not)
                (~literal fixnum?)
                (~literal integer?)
                (~literal even?)
                (~literal odd?)
                (~literal rational?)
                (~literal exact?)
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
                (~literal boolean?)
                (~literal path-string?)
                (~literal non-empty-string?)
                (~literal string?)
                (~literal symbol?)
                (~literal keyword?)
                (~literal char?)
                (~literal null?)
                (~literal void?)
                (~literal eof-object?)
                (~literal immutable?)
                (~literal list?)
                (~literal byte?)
                (~literal bytes?)
                (~literal complex?)
                (~literal float-complex?)
                (~literal extflonum?)
                (~literal flvector?)
                (~literal extflvector?)
                (~literal fxvector?)
                (~literal sequence?)
                (~literal pseudo-random-generator?)
                (~literal pseudo-random-generator-vector?)
                (~literal regexp?)
                (~literal pregexp?)
                (~literal byte-regexp?)
                (~literal byte-pregexp?)
                (~literal bytes-converter?)
                (~literal input-port?)
                (~literal output-port?)
                (~literal port?)
                (~literal path?)
                (~literal pair?)
                (~literal list?)
                (~literal placeholder?)
                (~literal hash-placeholder?)
                (~literal stream?)
                (~literal vector?)
                (~literal hash?)
                (~literal hash-equal?)
                (~literal hash-eqv?)
                (~literal hash-eq?)
                (~literal hash-weak?)
                (~literal hash-empty?)
                (~literal set?)
                (~literal generic-set?)
                (~literal set-eq?)
                (~literal set-eqv?)
                (~literal set-equal?)
                (~literal set-mutable?)
                (~literal set-weak?)
                (~literal set-empty?)
                (~literal arity-at-least?)
                (~literal normalized-arity?)
                (~literal procedure-arity?)
                (~literal procedure?)
                (~literal primitive?)
                (~literal stream-empty?)
                (~literal contract?)
                (~literal flat-contract?)
                (~literal list-contract?)
                (~literal has-contract?)
                (~literal has-blame?)
                (~literal blame?)
                (~literal generator?)
                (~literal dict?)
                (~literal struct-type?)
                (~literal struct-type-property?)
                (~literal unsupplied-arg?)
                (~literal continuation-mark-key?)
                (~literal weak-box?)
                (~literal box?)
                (~literal srcloc?)
                (~literal module-path-index?)
                (~literal module-path?)
                
                (~literal z:stx-obj?)
                (~literal z:compilation-top?)
                (~literal z:module-binding?)
                (~literal z:decoded-module-binding?)
                (~literal z:zo?)
                (~literal z:prefix?)
                (~literal z:stx?)
                (~literal z:global-bucket?)
                (~literal z:module-variable?)
                (~literal z:function-shape?)
                (~literal z:struct-shape?)
                (~literal z:struct-type-shape?)
                (~literal z:constructor-shape?)
                (~literal z:predicate-shape?)
                (~literal z:accessor-shape?)
                (~literal z:mutator-shape?)
                (~literal z:struct-type-property-shape?)
                (~literal z:property-predicate-shape?)
                (~literal z:property-accessor-shape?)
                (~literal z:struct-other-shape?)
                (~literal z:toplevel?)
                (~literal z:form?)
                (~literal z:expr?)
                (~literal z:seq?)
                (~literal z:inline-variant?)
                (~literal z:mod?)
                (~literal z:provided?)
                (~literal z:def-syntaxes?)
                (~literal z:seq-for-syntax?)
                (~literal z:def-values?)
                (~literal z:provided?)
                (~literal z:req?)
                (~literal z:splice?)
                (~literal z:lam?)
                (~literal z:closure?)
                (~literal z:case-lam?)
                (~literal z:let-one?)
                (~literal z:let-void?)
                (~literal z:install-value?)
                (~literal z:let-rec?)
                (~literal z:boxenv?)
                (~literal z:localref?)
                (~literal z:toplevel?)
                (~literal z:topsyntax?)
                (~literal z:application?)
                (~literal z:branch?)
                (~literal z:with-cont-mark?)
                (~literal z:beg0?)
                (~literal z:varref?)
                (~literal z:assign?)
                (~literal z:apply-values?)
                (~literal z:with-immed-mark?)
                (~literal z:primval?)
                (~literal z:wrap?)
                (~literal z:module-shift?)
                (~literal z:scope?)
                (~literal z:multi-scope?)
                (~literal z:binding?)
                (~literal z:module-binding?)
                (~literal z:decoded-module-binding?)
                (~literal z:local-binding?)
                (~literal z:free-id=?-binding?)
                (~literal z:all-from-module?)
                )))

(define-syntax-class ff
  #:description "restricted first-order function contracts"
  (pattern ((~literal ->) _:fc ... _:fd))
  (pattern ((~literal ->*) (_:fc ...) #:rest _:rc _:fd)))

(define-syntax-class fd
  #:description "restricted first-order function range"
  (pattern _:fc)
  (pattern ((~literal values) _:fc _:fc _:fc ...)))

(define liftable-base?
  ;; Ones that fit in implementation's `Base`
  (syntax-parser
    [(~or (~literal not)
          (~literal fixnum?)
          (~literal integer?)
          (~literal rational?)
          (~literal real?)
          (~literal number?)
          (~literal positive?)
          (~literal negative?)
          (~literal zero?)
          (~literal exact?)
          (~literal inexact?)
          (~literal inexact-real?)
          (~literal exact-integer?)
          (~literal exact-positive-integer?)
          (~literal exact-nonnegative-integer?)
          (~literal exact-integer?)
          (~literal flonum?)
          (~literal single-flonum?)
          (~literal boolean?)
          (~literal path-string?)
          (~literal string?)
          (~literal symbol?)
          (~literal keyword?)
          (~literal char?)
          (~literal null?)
          ;(~literal void?) ; shouldn't 
          (~literal eof-object?)
          (~literal immutable?)
          (~literal byte?)
          (~literal bytes?)
          (~literal complex?)
          (~literal float-complex?)
          (~literal extflonum?)
          (~literal regexp?)
          (~literal pregexp?)
          (~literal byte-regexp?)
          (~literal byte-pregexp?)
          (~literal path?))
     #t]
    [_ #f]))

(define for-TR
  (syntax-parser
    [(~literal integer?) #'exact-nonnegative-integer?]
    [o #'o]))

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
  (define rng-len
    (match-lambda
      ['any #f]
      [l (length l)]))
  (define sig-shape
    (syntax-parser
      [((~literal ->) dom ... rng:d)
       (values (length (syntax->list #'(dom ...)))
               (rng-len (attribute rng.values)))]
      [((~literal ->*) (dom ...) #:rest _ rng:d)
       (values (arity-at-least (length (syntax->list #'(dom ...))))
               (rng-len (attribute rng.values)))]
      [((~literal ∀/c) c) (sig-shape #'c)]
      [_
       ;; TODO generalize checks for case->
       (values #f #f)]))
  (define-values (num-args num-rng) (sig-shape sig))
  (when (and num-args num-rng)
    (for ([sigᵢ (in-list sigs)])
      (define-values (num-argsᵢ num-rngᵢ) (sig-shape sigᵢ))
      (unless (and num-argsᵢ
                   num-rngᵢ
                   (arity-compatible? num-args num-argsᵢ)
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

;; Convert contract range into list of refinement syntax
(define/contract (range->refinement rng)
  (syntax? . -> . (listof syntax?))
  (syntax-parse rng
    [((~literal and/c) cᵢ ...)
     (append-map range->refinement (syntax->list #'(cᵢ ...)))]
    [((~literal or/c) _ ...)
     (raise-syntax-error 'def "or/c in #:refinement clause not supported" rng)]
    [((~literal not/c) d)
     (cond [(identifier? #'d) (list #'(-not/c 'd))]
           [else
            (raise-syntax-error 'def "only identifier can follow not/c in refinement clause" rng)])]
    [((~literal cons/c) _ _)
     (raise-syntax-error
      'def
      (format "~a: cons/c in range not suported for now" (syntax-e #'o))
      rng)]
    [((~literal =/c) x:number) (list #''real? #'(-b x))]
    [((~literal >/c) x:number) (list #''real? #'(->/c x))]
    [((~literal >=/c) x:number) (list #''real? #'(-≥/c x))]
    [((~literal </c) x:number) (list #''real? #'(-</c x))]
    [((~literal <=/c) x:number) (list #''real? #'(-≤/c x))]
    [x:lit (list #'(-b x))]
    [(~literal any/c) '()]
    [(~literal none/c)
     (raise-syntax-error 'def "refinement clause does not accept none/c in range" rng)]
    [c:id (list #''c)]))

(define (prefix-id id [src id]) (format-id src ".~a" (syntax-e id)))
