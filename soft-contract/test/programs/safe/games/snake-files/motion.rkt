#lang racket/base

(require racket/contract
         "data.rkt")
(define g6 (lambda (x) (equal? x (void))))
(define g7 (lambda (x) (world? x)))
(define g8 '"up")
(define g9 '"down")
(define g10 '"left")
(define g11 '"right")
(define g12 (or/c g8 g9 g10 g11))
(define generated-contract3 (-> (values g6)))
(define generated-contract4 (-> g7 (values g7)))
(define generated-contract5 (-> g7 g12 (values g7)))
(provide (contract-out
          (world->world generated-contract4)
          (world-change-dir generated-contract5)
          (reset! generated-contract3)))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require "data-adaptor.rkt")
(require "const.rkt")
(require "data.rkt")
(require "motion-help.rkt")
(provide)
(define r (make-pseudo-random-generator))
(define (reset!) (void))

(define (world->world w)
  (cond
    ((eating? w) (snake-eat w))
    (else (world (snake-slither (world-snake w)) (world-food w)))))

(define (eating? w)
  (posn=? (world-food w) (car (snake-segs (world-snake w)))))

(define (snake-change-direction snk dir) (snake dir (snake-segs snk)))

(define (world-change-dir w dir)
  (world (snake-change-direction (world-snake w) dir) (world-food w)))

(define (snake-eat w)
  (define i (add1 (random (sub1 BOARD-WIDTH) r)))
  (define j (add1 (random (sub1 BOARD-HEIGHT) r)))
  (world (snake-grow (world-snake w)) (posn i j)))
(provide)
