#lang racket/base

(require "fake-contract.rkt" ; instead of `racket/contract` to help parser
         (rename-in racket/base [provide real:provide])
         racket/match
         syntax/parse/define
         (only-in typed/racket assert)
         (for-syntax racket/base
                     racket/match
                     racket/syntax
                     syntax/parse))

(real:provide ;; Run-time
         trivial
         induct-on
         assert
         ;; DSL
         forall (rename-out [forall ∀])
         (rename-out [parametric->/c ∀/c])
         define-theorem
         ↑)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Run-time library
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define trivial (λ _ 'trivally-automated))

;; Assume primitive `induct-on` that can inspect contracts
;; and produce induction principles for *some* contracts
;; deemed to specify inductive data
;; (e.g. naturals, and many ad-hoc recursive contracts
;; whose recursive references follow immutable struct fields)
(define induct-on
  (let ()

    (define/contract nat-induct
      (->i ([x exact-nonnegative-integer?]
            [P (exact-nonnegative-integer? . -> . contract?)]
            [on-0 {P} (->i ([x 0]) (_ {x} (P x)))]
            [on-n {P} (->i ([n exact-nonnegative-integer?] [ih {n} (P n)])
                           (_ {n} (P (+ 1 n))))])
           (_ {x P} (P x)))
      (λ (n P on-0 on-n)
        (case n
          [(0)  (on-0 0)]
          [else (on-n (- n 1) (nat-induct (- n 1) P on-0 on-n))])))

    (define/contract list-induct
      (->i ([xs list?]
            [P (list? . -> . contract?)]
            [on-null {P} (->i ([x null?]) (_ {x} (P x)))]
            [on-cons {P} (->i ([x.car any/c] [x.cdr list?] [ih {x.cdr} (P x.cdr)])
                              (_ {x.car x.cdr} (P (cons x.car x.cdr))))])
           (_ {xs P} (P xs)))
      (λ (l P on-null on-cons)
        (match l
          ['() (on-null '())]
          [(cons x l*) (on-cons x l* (list-induct l* P on-null on-cons))])))
    
    (match-lambda
      [(== exact-nonnegative-integer?) nat-induct]
      [(== list?) list-induct]
      [c (error 'induct-on "no implementation for ~a" c)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof DSL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(begin-for-syntax
  (define-syntax-class forall-dom
    #:description "universal quantifier's domain"
    #:attributes (names domain)
    (pattern x:id                   #:attr names #'(x) #:attr domain #'any/c)
    (pattern [x:id y:id ... c:expr] #:attr names #'(x y ...) #:attr domain #'c)))

(define-syntax forall
  (syntax-parser
    [(forall (d:forall-dom ...) e:expr)
     (define-values (doms deps)
       (let go ([doms #'(d ...)] [deps '()])
         (syntax-parse doms
           [() (values '() deps)]
           [(d:forall-dom d* ...)
            (with-syntax ([(x ...) #'d.names]
                          [c #'d.domain])
              (define deps* (append deps (syntax->list #'(x ...))))
              (define-values (doms* deps**) (go #'(d* ...) deps*))
              (values (foldr (λ (x doms)
                               (if (null? deps)
                                   (cons #`(#,x c) doms)
                                   (cons #`(#,x #,deps c) doms)))
                             doms*
                             (syntax->list #'(x ...)))
                      deps**))])))
     #`(->i #,doms (_ #,@(if (null? deps) '() (list deps)) (λ _ e)))]))

(define-syntax define-theorem
  (syntax-parser
    [(_ (f:id d:forall-dom ...)
        #:conclusion c:expr
        (~optional (~seq #:proof e:expr)
                   #:defaults ([e #''trivally-automated])))
     (with-syntax ([((x ...) ...) #'(d.names ...)])
       #'(define/contract f (forall (d ...) c)
           (λ (x ... ...) e)))]
    [(_ f:id c:expr
        (~optional (~seq #:proof e:expr)
                   #:defaults ([e #'trivial])))
     #'(define/contract f c e)]))

(define-syntax-rule (↑ e) (λ (_) e))

(module+ test
  (require (only-in racket/contract contract-exercise))
  (define-theorem add1-mono
    (forall ([m integer?] [n (and/c integer? (>=/c m))]) (>= (add1 n) (add1 m))))
  (define-theorem rev-id
    (forall (x) (equal? (reverse (list x)) (list x))))
  (define-theorem app-assoc
    (forall ([xs ys zs list?])
       (equal? (append (append xs ys) zs) (append xs (append ys zs)))))
  (contract-exercise add1-mono rev-id app-assoc))
