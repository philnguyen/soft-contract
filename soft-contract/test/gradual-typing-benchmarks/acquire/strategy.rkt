#lang racket

;; ---------------------------------------------------------------------------------------------------
;; implementing Acquire game strategies

(provide
 ordered-s
 random-s
)

;; ---------------------------------------------------------------------------------------------------
;; IMPLEMENTATION

(require
 "../base/untyped.rkt"
 "board.rkt"
 "state.rkt"
 )
(require (only-in "basics.rkt"
  ALL-HOTELS
  SHARES-PER-TURN#
  hotel<=?
  price-per-share
  shares++
  shares--
  shares-available
))
(require (only-in "auxiliaries.rkt"
  randomly-pick
))

(define nat-SHARES-PER-TURN# (assert SHARES-PER-TURN# exact-nonnegative-integer?))

;; =============================================================================

;; (cons Hotel [Listof Hotel]) -> Hotel
(define (alphabetically-first w)
  (first (sort w hotel<=?)))

(define (pick-hotel b to-place kind available-hotels select-founding-hotel select-merger)
  (cond
    [(eq? FOUNDING kind)
     (and (cons? available-hotels) (select-founding-hotel available-hotels))]
    [(eq? MERGING kind)
     (define-values (w _) (merging-which b to-place))
     (select-merger w)]
    [else #f]))

;; Board Cash Shares N [ [Listof Hotel] -> [Listof Hotel] ] -> [Listof Hotel]
;; buy N hotels in alphabetical order that fit into budget
(define (to-buy b my-cash available-shares BUY-N)
  (let loop
       ((hotels  ALL-HOTELS)
        (n  0)
        (to-buy  '())
        (cash  my-cash)
        (as  available-shares))
    (cond 
      [(or (empty? hotels) (= BUY-N n)) (reverse to-buy)]
      [else 
       (define h (first hotels))
       (define available-h (shares-available as h))
       (cond
         [(= 0 available-h) (loop (rest hotels) n to-buy cash as)]
         [else (define price (price-per-share h (size-of-hotel b h)))
               (if (and price (<= price cash))
                   (if (and (<= (* 2 price) cash) (> available-h 1))
                       (list h h)
                       (list h))
                   (loop (rest hotels) n to-buy cash as))])])))

[define (strategy/d choose-founding choose-merger choose-shares#)
  (lambda (turn)
    (define b (get-field board turn))
    (define my-cash (get-field cash turn))
    (define available-shares (get-field shares turn))
    (define available-hotels (get-field hotels turn))
    (define tile-kind
      (for/or 
              ((t  (sort (get-field tiles turn) tile<=?)))
        (let ([s (what-kind-of-spot b t)])
          (and (not (eq? s IMPOSSIBLE))
               (list t s)))))
    (cond 
      [tile-kind
       (define-values (to-place kind) (values (car tile-kind) (cadr tile-kind)))
       (define hotel  (pick-hotel b to-place kind available-hotels choose-founding choose-merger))
       (define board  (set-board b to-place kind hotel))
       (define shares 
         (if (and (eq? FOUNDING kind) hotel (> (shares-available available-shares hotel) 0))
             (shares-- available-shares hotel)
             available-shares))
       (when (and (eq? MERGING kind) hotel) ;;bg; checks for hotel
         ;; ignore the decisions of the other players
         (send turn place to-place hotel))
       (define buy
               (to-buy board my-cash shares nat-SHARES-PER-TURN#))
       (values to-place hotel buy)]
      [else
       (define buy 
         (to-buy b my-cash available-shares (choose-shares# nat-SHARES-PER-TURN#)))
       (values #f #f buy)]))]

(define (id x) x)

(define ordered-s
  (strategy/d first alphabetically-first id))

(define (random+1 n)
  (random (+ n 1)))

(define random-s
  (strategy/d randomly-pick randomly-pick random+1))

