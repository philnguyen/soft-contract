#lang racket/base

;; a representation of the complete deck of cards 

(provide
 ;;   { [Listof X] -> [Listof X] }
 ;;   { -> Bulls }
 ;; -> CardPool
 ;; create and organize the pool of cards in a random order so that
 ;; the dealer can hand cards to players and create the initial deck
 ;;
 ;; so we can keep things deterministic 
 ;; the first optional argument is a shuffle algorithm for lists
 ;; the second optional argument generates bulls 
 create-card-pool)

;; -----------------------------------------------------------------------------

(require
  racket/class
  "../base/untyped.rkt"
  (only-in racket/list shuffle first rest))
(require "card.rkt")
(require (only-in "basics.rkt"
  FACE
  HAND
  MIN-BULL
  MAX-BULL
))

;; For the assert
(define (hand? h)
  (and (list? h)
       (= 10 (length h))
       (for/and ([c (in-list h)]) (card? c))))

;; ---------------------------------------------------------------------------------------------------
(define (create-card-pool (shuffle shuffle) (random-bulls random-bulls))
  (new card-pool% (shuffle shuffle) (random-bulls random-bulls)))

;; -> Bulls
;; pick a random number of BULLS 
(define (random-bulls)
  (assert (random MIN-BULL (+ MAX-BULL 1)) bulls?))

(define card-pool%
  (class object%
    (init-field (shuffle shuffle) (random-bulls random-bulls))
    (super-new)

    (define my-cards
      (shuffle (build-list FACE (lambda (i) (card (assert (+ i 1) face?) (random-bulls))))))

    (define/public (draw-card)
      (begin0 (first my-cards)
              (set! my-cards (rest my-cards))))

    (define/public (draw-hand)
      (assert (build-list HAND (lambda (_) (draw-card))) hand?))))
