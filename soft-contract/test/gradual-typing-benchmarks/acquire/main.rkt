#lang racket/base
(random-seed 5)

;; This is `tree-game.rkt`

;; -----------------------------------------------------------------------------

(require
  racket/list
  racket/class
  "board.rkt"
  "state.rkt"
)
(require (only-in "admin.rkt"
  administrator%
))
(require (only-in "player.rkt"
 random-players
 ordered-players
 inf-loop-player
))
(require (only-in "auxiliaries.rkt"
  randomly-pick
))

;; =============================================================================

(define (go extra)
  (define p0 (ordered-players 10))
  (define p1 (random-players 10))
  (define p (cons extra (append p0 p1)))
  (define-values (two-status _score two-run)
    (let ([r (run p 10 #:show show #:choice randomly-pick)])
      (values (car r) (cadr r) (caddr r))))
  ;(displayln `(,(length two-run) ,two-status))
  (void))

(define (run players turns# #:show (show show) #:choice (choose-next-tile first))
  (define a (new administrator% (next-tile choose-next-tile)))
  (for ((p players)) (send p go a))
  (send a run turns# #:show show))

;; -> (Nat Board -> Void)
(define (show)
  (void))

(define (main n)
  (for ((i (in-range n)))
    (go (inf-loop-player 99))))

(time (main 10))
