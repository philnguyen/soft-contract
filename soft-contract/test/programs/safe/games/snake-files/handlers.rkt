#lang racket/base

(require racket/contract
         "data.rkt")
(define g5 (lambda (x) (world? x)))
(define g6 '#t)
(define g7 '#f)
(define g8 (or/c g6 g7))
(define g9 string?)
(define generated-contract3 (-> g5 (values g8)))
(define generated-contract4 (-> g5 g9 (values g5)))
(provide (contract-out
          (handle-key generated-contract4)
          (game-over? generated-contract3)))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require "data-adaptor.rkt")
(require "collide.rkt")
(require "motion.rkt")

(define (handle-key w ke)
  (cond
    ((equal? ke "w") (world-change-dir w "up"))
    ((equal? ke "s") (world-change-dir w "down"))
    ((equal? ke "a") (world-change-dir w "left"))
    ((equal? ke "d") (world-change-dir w "right"))
    (else w)))

(define (game-over? w)
  (or (snake-wall-collide? (world-snake w))
      (snake-self-collide? (world-snake w))))
(provide)
