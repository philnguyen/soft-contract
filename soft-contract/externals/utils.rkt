#lang racket/base

(provide (all-defined-out)
         prefix-id)

(require racket/base
         racket/match
         racket/list
         racket/syntax
         racket/contract
         racket/splicing
         syntax/parse
         syntax/parse/define
         (only-in "../utils/pretty.rkt" n-sub)
         "../primitives/utils.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         (for-template racket/base
                       racket/contract
                       racket/syntax
                       syntax/parse
                       "../ast/definition.rkt"
                       "../runtime/main.rkt"))

(define-syntax-class fun
  #:description "restricted higher-order function signature"
  (pattern c:arr
           #:attr init (attribute c.init)
           #:attr arity (attribute c.arity)
           #:attr rng (attribute c.rng))
  (pattern c:dep
           #:attr init (attribute c.init)
           #:attr arity (attribute c.arity)
           #:attr rng (attribute c.rng)))

(define-syntax-class hc
  #:description "restricted higher-order contract"
  (pattern _:arr)
  (pattern _:dep)
  (pattern _:fc))

(define-syntax-class arr
  #:description "restricted higher-order non-dependent contract"
  (pattern ((~literal ->) c:hc ... d:hc)
           #:attr init (syntax->list #'(c ...))
           #:attr arity (length (syntax->list #'(c ...)))
           #:attr rng #'d))

(define-syntax-class dep
  #:description "restricted higher-order dependent contract"
  (pattern ((~literal ->i)
            ([x:id c:hc] ...)
            ((~literal res) (y:id ...) d:hc))
           #:fail-when
           (let ([xs (syntax->list #'(x ...))]
                 [ys (syntax->list #'(y ...))])
             (not (and (equal? (length xs) (length ys))
                       (andmap free-identifier=? xs ys))))
           "->i: variables in (res ...) must be identical list as all binders for now"
           #:attr init (syntax->list #'(c ...))
           #:attr arity (length (syntax->list #'(c ...)))
           #:attr rng #'d))
