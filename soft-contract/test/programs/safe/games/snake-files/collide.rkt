#lang racket/base

(require racket/contract
         "data.rkt")
(define g5 (lambda (x) (snake? x)))
(define g6 '#t)
(define g7 '#f)
(define g8 (or/c g6 g7))
(define generated-contract3 (-> g5 (values g8)))
(define generated-contract4 (-> g5 (values g8)))
(provide (contract-out
          (snake-self-collide? generated-contract3)
          (snake-wall-collide? generated-contract4)))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require "data-adaptor.rkt")
(require "const.rkt")
(require "data.rkt")

(define (snake-wall-collide? snk) (head-collide? (car (snake-segs snk))))

(define (head-collide? p)
  (or (<= (posn-x p) 0)
      (>= (posn-x p) BOARD-WIDTH)
      (<= (posn-y p) 0)
      (>= (posn-y p) BOARD-HEIGHT)))

(define (snake-self-collide? snk)
  (segs-self-collide? (car (snake-segs snk)) (cdr (snake-segs snk))))

(define (segs-self-collide? h segs)
  (cond
    ((null? segs) #f)
    (else (or (posn=? (car segs) h) (segs-self-collide? h (cdr segs))))))
(provide)
