#lang racket/base
(require racket/contract)

(define-syntax-rule (define2 x ctc e)
  (begin
    (define x e)
    (provide (contract-out [x ctc]))))

(define2 g (between/c 1 10) 8)
