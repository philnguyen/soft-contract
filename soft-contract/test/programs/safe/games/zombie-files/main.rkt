#lang racket/base

(require racket/contract)
(module require/contracts racket/base
  (require racket/contract)
  (define g5 real?)
  (define g6 (or/c g5))
  (define g7 string?)
  (define g8 '())
  (define g9 (cons/c g7 g8))
  (define g10 (cons/c g6 g9))
  (define g11 (cons/c g6 g10))
  (define g12 any/c)
  (define g13 (listof g12))
  (define l/10 g11)
  (define l/11 g13)
  (provide l/10 g12 g13 l/11 g5 g6 g7 g8 g9 g10 g11))
(require (prefix-in -: (only-in 'require/contracts))
         (except-in 'require/contracts))

(require require-typed-check "image-adapted.rkt")
(begin (require "zombie.rkt") (void))

(define (replay w0 hist)
  (let loop ([w w0] [h hist])
    (cond
      ((null? h) (void))
      ((not (list? (car h))) (error "input error"))
      (else
       (define m (caar h))
       (define as (cdar h))
       (case m
         ((on-mouse)
          (define r
            (apply (world-on-mouse w) as))
          (loop r (cdr h)))
         ((on-tick) (define r ((world-on-tick w))) (loop r (cdr h))))))))
(define TEST (with-input-from-file "../base/zombie-hist.rktd" read))

(define (main hist)
  (cond
    ((list? hist) (for ((i (in-range 100))) (replay w0 hist)))
    (else (error "bad input"))))
(time (main TEST))
