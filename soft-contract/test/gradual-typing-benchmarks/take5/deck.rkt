#lang racket/base

;; representing the deck of STACKS stack on the table 

(provide
 ;; CardPool -> Deck 
 create-deck)

;; -----------------------------------------------------------------------------

(require
  racket/class
  racket/list
  "../base/untyped.rkt"
  "card.rkt"
)

(require (only-in "basics.rkt"
  FACE
  STACKS
))
(require (only-in "stack.rkt"
  bulls
))

;; For the assert
(define (stack? s)
  (and (list? s)
    (for/and ((x (in-list s))) (card? x))
    (let ((l (length s)))
      (and (< 0 l) (< l 6)))))

;; ---------------------------------------------------------------------------------------------------

(define (create-deck card-pool)
  (define deck% (for-player (for-dealer base-deck%)))
  (define cards (build-list STACKS (lambda (_) (send card-pool draw-card))))
  (new deck% [cards0 cards]))

;; Class[my-stacks field] -> Class[my-stacks field and fewest-bulls method]
(define (for-player deck%)
  (class deck%
    (inherit-field my-stacks)
    (super-new)

    (define/public (fewest-bulls)
      (define stacks-with-bulls
        (for/list
                  ((s my-stacks))
          (list s (bulls s))))
      (first (argmin (lambda (l) (second l)) stacks-with-bulls)))))

;; Class[cards0 field] -> Class[fit, push, replace & larger-than-some-top-of-stacks? methods]
(define (for-dealer deck%)
  (class deck%
    (inherit-field cards0)
    (inherit-field my-stacks)
    (super-new)

    ;; [Listof Stack]
    (set-field! my-stacks this (map (lambda (c) (list c)) cards0))
    ;(field [my-stacks

    (define/public (fit c)
      (define (distance stack)
        (define d (first stack))
        (if (>-face c d) (--face c d) (+ FACE 1)))
      (argmin distance my-stacks))

    (define/public (push c)
      (define s0 (fit c))
      (void (replace-stack (first s0) c)))

    (define/public (replace s c)
      (replace-stack (first s) (list c)))

    (define/public (replace-stack top0 c)
      (define result  0)
      (set! my-stacks 
            (for/list  ((s  my-stacks))
              (cond
                [(equal? (first s) top0)
                 (set! result (bulls s))
                 (assert
                  (if (cons? c)
                   c
                   (cons c s))
                  stack?)]
                [else s])))
      result)

    (define/public (larger-than-some-top-of-stacks? c)
      (for/or ((s my-stacks))
        (>-face c (first s))))))

;; Class[cards0 field]
(define base-deck%
  (class object%
    (init-field
     ;; [Listof Card]
     ;; the tops of the initial stacks (for a round)
     cards0)

    (field (my-stacks '()))

    (super-new)))
