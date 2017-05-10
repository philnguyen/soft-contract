#lang racket

;; ---------------------------------------------------------------------------------------------------
;; Acquire player that manages all the interactions; delegates decision making to separate strategies 

(provide
 random-players
 ordered-players
 inf-loop-player
 )

;; ---------------------------------------------------------------------------------------------------
;; IMPLEMENTATION 

(require
 "../base/untyped.rkt"
 "state.rkt"
)
(require (only-in "admin.rkt"
  administrator%
  turn%
))
(require (only-in "basics.rkt"
  player-shares0
  *combine-shares
  shares-minus
  banker-shares0
))
(require (only-in "strategy.rkt"
  ordered-s
  random-s
))

;; -----------------------------------------------------------------------------

;; (define (player? x)
;;   (is-a? x player%))

(define (create n c)
  (new player% [name n][choice c]))

(define player%
  (class object%
    (init-field name choice)
    (super-new)
    
    (field [*players '()]
           [*bad '()])

    (define *my-game-name "")
    
    (define/public (go administrator)
      (set! *my-game-name (send administrator sign-up name this)))
    
    (define/public (setup s)
      (bad-players (state-players s)))
    
    (define/public (take-turn turn) 
      (bad-players (get-field players turn))
      ;; reconcile is added for remote players that don't get complete information
      (choice (reconcile turn)))
      ;; (define-values (to-place hotel shares-to-buy) 
      ;; (values to-place hotel shares-to-buy))
    
    (define/public (keep hotels)
      (map (lambda (h) (< (random 100) 50)) hotels))
    
    (define/public (receive-tile t)
      (void))
    
    (define/public (inform s)
      (bad-players (state-players s)))
    
    (define/public (the-end state results)
      ;; I should figure out what to do here 
      (void))
    
    ;; [Listof Players] -> Void
    ;; given the list of current players, find out which ones dropped out since the last update
    ;; effect: move the drop-out players to this.*bad, keep the good ones in this.*players
    (define/private (bad-players players)
      (set! *bad 
            (for/fold
                      ([bad  *bad])
                      ((old-player  (in-list *players))) 
              (define n (player-name old-player))
              (if (findf (lambda (current)
                           (string=? (player-name current) n)) players)
                  bad
                  (cons old-player bad))))
      (set! *players players))
    
    ;; Turn -> Turn 
    ;; effect: reduce the turn's banker-shares by the shares of this.*bad players
    (define/private (reconcile turn)
      (define bad-shares (*combine-shares (map player-shares *bad)))
      (send turn reconcile-shares bad-shares)
      turn)))

;; -----------------------------------------------------------------------------
;; from `player-factory.rkt`

(define (players S n)
  (for/list ((name '("a" "b" "c" "d" "e" "f")) (i (in-range n))) (create name S)))

(define (random-players n)
  (players random-s n))

(define (ordered-players n)
  (players ordered-s n))

(define (inf-loop-player n)
  (define m 0)
  (define (S t)
    (if (> n m)
        (begin (set! m (+ m 1)) (ordered-s t))
        (let L () (L))))
  (create (format "inf loop after ~a" n) S))

