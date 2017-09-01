#lang racket/base

(provide (all-defined-out))

(require racket/base
         racket/match
         racket/list
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
  (pattern _:fc))

(define-syntax-class d
  #:description "restricted contract range"
  (pattern _:c)
  (pattern ((~literal values) d₁:c d₂:c d*:c ...))
  (pattern (~literal any)))

(define-syntax-class hc
  #:description "restricted higher-order-contract"
  (pattern _:poly-hc)
  (pattern _:mono-hc))

(define-syntax-class poly-hc
  #:description "restricted polymorphic function contract"
  (pattern ((~literal ∀/c) (_:id ...) _:mono-hc)))

(define-syntax-class mono-hc
  #:description "restricted monomorphic function contract"
  (pattern ((~literal ->) _:c ... _:d))
  (pattern ((~literal ->*) _:c ... #:rest _:c _:d))
  (pattern ((~literal case->)
            [(~literal ->)
             _:c ... (~optional (~seq #:rest r:c) #:defaults ([r #f])) _:d]
            ...)))

(define-syntax-class fc
  #:description "restricted first-order contract"
  (pattern _:id) ; seal reference
  (pattern _:o)
  (pattern _:lit)
  (pattern ((~literal not/c) _:fc))
  (pattern ((~or (~literal >/c)
                 (~literal </c)
                 (~literal =/c)
                 (~literal >=/c)
                 (~literal <=/c)) r:number)
           #:when (real? (syntax-e #'r))))

(define-syntax-class mc
  #:description "restricted ambig-order contract"
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
  ;; Ones that fit in implementation's `Base`
  (pattern (~or (~literal integer?)
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
                (~literal immutable?))))

(define-syntax-class ff
  #:description "restricted first-order function contracts"
  (pattern ((~literal ->) _:fc ... _:fd))
  (pattern ((~literal ->*) _fc ... #:rest _:fc _:fd)))

(define-syntax-class fd
  #:description "restricted first-order function range"
  (pattern _:fc)
  (pattern ((~literal values) _:fc _:fc _:fc ...)))

(define/contract range-components (syntax? . -> . (listof syntax?))
  (syntax-parser
    [((~literal values) c ...) (syntax->list #'(c ...))]
    [c (list #'c)]))

(define/contract range-arity (syntax? . -> . exact-nonnegative-integer?) (compose length range-components))

(define/contract in-syntax-list (syntax? . -> . sequence?) (compose in-list syntax->list))

(define/contract (check-shape-ok o sig sigs)
  (identifier? syntax? (listof syntax?) . -> . any)
  (define sig-shape
    (syntax-parser
      [((~literal ->) dom ... rng)
       (values (length (syntax->list #'(dom ...))) (range-arity #'rng))]
      [((~literal ->*) dom ... #:rest _ rng)
       (values (arity-at-least (length (syntax->list #'(dom ...))))
               (range-arity #'rng))]
      [((~literal ∀/c) c) (sig-shape #'c)]
      [_
       ;; TODO generalize checks for case->
       (values #f #f)]))
  (define-values (num-args num-rng) (sig-shape sig))
  (when (and num-args num-rng)
    (for ([sigᵢ (in-list sigs)])
      (define-values (num-argsᵢ num-rngᵢ) (sig-shape sigᵢ))
      (unless (and (arity-includes? num-args num-argsᵢ)
                   (= num-rng num-rngᵢ))
        (raise-syntax-error (syntax-e #'o) "incompatible shape" sig (list sigᵢ))))))

(define-simple-macro (define-parameter/contract [x:id c v] ...)
  (begin (define/contract x (parameter/c c) (make-parameter v)) ...))

(define/contract (gen-ids src prefix n)
  ((or/c #f syntax?) (or/c symbol? string?) integer? . -> . (listof identifier?))
  (for/list ([i (in-range n)])
    (format-id src "~a~a" prefix (n-sub i))))

#|
(def o _:hc)
-->
(: o : -⟦f⟧)
(define (o ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
  
  (: check-arg : -W¹ -Γ → (℘ -ς))
  (define (check-arg W Γ)
    )

  (cond
    [(arity-ok? _ (length Ws))
     (check-arg W₁ Γ)]
    [blm]))

|#
