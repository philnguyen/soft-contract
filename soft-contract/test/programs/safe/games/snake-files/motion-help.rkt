#lang racket/base

(require racket/contract
         "data.rkt")
(define g5 (lambda (x) (snake? x)))
(define generated-contract3 (-> g5 (values g5)))
(define generated-contract4 (-> g5 (values g5)))
(provide (contract-out
          (snake-grow generated-contract3)
          (snake-slither generated-contract4)))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require "data-adaptor.rkt")
(require "cut-tail.rkt")

(define (next-head seg dir)
  (cond
    ((equal? "right" dir) (posn (add1 (posn-x seg)) (posn-y seg)))
    ((equal? "left" dir) (posn (sub1 (posn-x seg)) (posn-y seg)))
    ((equal? "down" dir) (posn (posn-x seg) (sub1 (posn-y seg))))
    (else (posn (posn-x seg) (add1 (posn-y seg))))))

(define (snake-slither snk)
  (let ((d (snake-dir snk)))
    (snake
     d
     (cons
      (next-head (car (snake-segs snk)) d)
      (cut-tail (snake-segs snk))))))

(define (snake-grow snk)
  (let ((d (snake-dir snk)))
    (snake
     d
     (cons (next-head (car (snake-segs snk)) d) (snake-segs snk)))))
(provide)
