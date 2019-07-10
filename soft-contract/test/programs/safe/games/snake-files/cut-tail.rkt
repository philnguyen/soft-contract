#lang racket/base

(require racket/contract
         "data.rkt")
(define g4 (lambda (x) (posn? x)))
(define g5 (listof g4))
(define g6 (cons/c g4 g5))
(define generated-contract3 (-> g6 (values g5)))
(provide (contract-out (cut-tail generated-contract3)))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require "data-adaptor.rkt")

(define (cut-tail segs)
  (let ((r (cdr segs)))
    (cond ((null? r) null) (else (cons (car segs) (cut-tail r))))))
(provide)
