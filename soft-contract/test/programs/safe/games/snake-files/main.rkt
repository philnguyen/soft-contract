#lang racket/base
(require racket/contract
         racket/match)
(provide (contract-out))
(module require/contracts racket/base
  (require racket/contract)
  (provide (contract-out)))
(require 'require/contracts)
(require "data-adaptor.rkt")
(require "const.rkt")
(require "motion.rkt")
(require "handlers.rkt")

(define (replay w0 hist)
  (reset!)
  (let loop ((w w0) (h hist))
    (if (null? h)
        w
        (let ()
          (loop
           (match
               (car h)
             (`(on-key ,(? string? ke)) (handle-key w ke))
             (`(on-tick) (world->world w))
             (`(stop-when) (game-over? w) w))
           (cdr h)))))
  (void))
(define DATA (with-input-from-file "../base/snake-hist.rktd" read))
(define LOOPS 200)

(define (main hist)
  (define w0 (WORLD))
  (cond
    ((list? hist) (for ((i (in-range LOOPS))) (replay w0 hist)))
    (else (error "bad input"))))
(time (main DATA))
