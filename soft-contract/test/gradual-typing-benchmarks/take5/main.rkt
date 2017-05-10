#lang racket/base

;; the main entry point for an OO implementation of "6 Nimmt!" (Take 5)

(provide
 main)

(require
  require-typed-check
  racket/class
  "../base/untyped.rkt"
)

(require (only-in "player.rkt"
  create-player
))
(require (only-in "dealer.rkt"
  create-dealer
))

(define (index? n)
  (and (exact-nonnegative-integer? n) (< n 9999999)))

;; =============================================================================

(define (main n)
  (define k
    (cond
      [(and (string? n) (string->number n))
       => (lambda (x) (assert n index?))]
      [(index? n) n]
      [else
       (error 'main "input must be a natural number; given ~e" n)]))
  (define players (build-list k create-player))
  (define dealer (create-dealer players))
  (send dealer play-game))

(define PLAYERS 10)
(define ITERS PLAYERS)

(module+ test
  (unless (equal? (main PLAYERS)
                  '((after-round 2)
                    ((1 0) (2 0) (3 0) (6 0) (7 0) (8 0) (0 56) (4 80) (9 80) (5 120))))
    (raise-user-error 'take5 "TEST FAILURE")))

(module+ main
  (time (for ([n (in-range ITERS)]) (main PLAYERS))))
