#lang racket

;; ---------------------------------------------------------------------------------------------------
;; basic game ontology and data structures for simple concepts (hotels, cash, shares)

;; ---------------------------------------------------------------------------------------------------
(provide
 hotel?
 ;; (-> Any Boolean)
 hotel<=?
 ;; (-> Hotel Hotel Boolean)
 
 ALL-HOTELS
 ;; (Listof Hotel), also sorted
 
 SAFE# FINAL#
 ;; Natural

 hotel->label
 ;; (-> Hotel String)

 hotel->color
 ;; (-> Hotel Symbol)

 shares?
 ;; (-> Any Boolean)

 banker-shares0
 ;; Shares

 player-shares0
 ;; Shares

 shares-order?
 ;; 

 SHARES-PER-TURN#
 ;; Natural

 shares++
 ;; (-> Shares Hotel Shares)

 (rename-out [ext:shares-- shares--])
 ;; (-> Shares Hotel Shares)
 ;; Precondition: (shares-available s h) > 0

 shares-available
 ;; (-> Shares Hotel Natural)

 (rename-out [ext:shares-available? shares-available?])
 ;; (-> Shares (Listof Hotel) Boolean)
 ;; Precondition: (shares-order? s*)
 ;; "Can the given order of shares be satisfied in this wallet?

 shares-minus
 ;; (-> Shares Shares Shares)

 shares-plus
 ;; (-> Shares Shares Shares)

 shares-compatible
 ;; (-> Shares (-> Shares Boolean))

 shares-combinable?
 ;; (-> (Listof Shares) Boolean)

 (rename-out [ext:*combine-shares *combine-shares])
 ;; (-> (Listof Shares) Shares)
 ;; Precondition: shares-combinable

 *create-shares
 ;; (-> Hotel Natural Shares)

 shares->string
 ;; (-> Shares String)

 cash?
 ;; (-> Any Boolean)

 CASH0
 ;; Cash

 price-per-share
 ;; (-> Hotel Natural (Option Cash))

 bonus
 ;; (-> M*rity Hotel Natural Cash)
)

;; ---------------------------------------------------------------------------------------------------

(require
  "../base/untyped.rkt"
)
(require (only-in "auxiliaries.rkt"
 randomly-pick
))

;; ---------------------------------------------------------------------------------------------------

(define MIN-PLAYER# 3)
(define MAX-PLAYER# 6)

(define SAFE# 12)
(define FINAL# 40)

(define AMERICAN    "American")
(define CONTINENTAL "Continental")
(define FESTIVAL    "Festival")
(define IMPERIAL    "Imperial")
(define SACKSON     "Sackson")
(define TOWER       "Tower")
(define WORLDWIDE   "Worldwide")

(define HOTELS
  `(,AMERICAN ,CONTINENTAL ,FESTIVAL ,IMPERIAL ,SACKSON ,TOWER ,WORLDWIDE))
(define HOTEL:C
  '(red      blue        green    yellow   purple  brown   orange))

;; Hotel  :: HOTELS 

(define (hotel? x)
  (cons? (member x HOTELS)))

(define hotel<=? string<=?)

(define ALL-HOTELS HOTELS)

(define random-hotel (lambda () (randomly-pick HOTELS)))

(define (hotel->color h)
  (define r
    (for/fold
              ([r  #f])
              ((i  (in-list HOTELS))
               (c  (in-list HOTEL:C)))
      (or r (and (equal? h i) c))))
  (or r 
      (error 'hotel->color (format "Unbound hotel ~a" h))))

(define (string->hotel n)
  (and n (member n HOTELS) n))

(define (hotel->label x)
  x)

;; ---------------------------------------------------------------------------------------------------
;; SHARES = [Hashof Hotel Nat]

(define SHARES0 25)
(define SHARES-PER-TURN# 2)

(define (listof-hotel? x)
  (and (list? x)
       (andmap hotel? x)))

;;bg; changed from shares-order/c
(define (shares-order? x*)
  (define h* (assert x* listof-hotel?))
  (and
   (not (null? h*))
   (let ([h1  (car h*)])
     (for/and
              ([h2  (in-list (cdr h*))])
       (string=? h1 h2)))
   (<= SHARES-PER-TURN# (length h*))))

(define player-shares0
  (make-hash (for/list
                       ([h (in-list ALL-HOTELS)])
               (cons h 0))))

(define banker-shares0
  (make-hash (for/list
                       ([h (in-list ALL-HOTELS)])
               (cons h SHARES0))))

(define (shares? x)
  (and (hash? x)
       (for/and ([(k v) (in-hash x)])
         (and (hotel? k)
              (exact-nonnegative-integer? k)))))

(define (shares-minus s t)
  (for/fold
            ((s  s))
            ([(hotel n) (in-hash t)])
    (hash-update s hotel (λ (m) (max 0 (- m n))))))

(define (shares-plus s t)
  (for/fold
            ((s s))
            ([(hotel n) (in-hash t)])
    (hash-update s hotel (λ (m) (+ m n)))))

(define (ext:shares-- s h)
  (unless (> (shares-available s h) 0)
    (error 'shares-- (format "Precondition failed: (> (shares-available ~a ~a) 0)" s h)))
  (shares-- s h))

(define (shares-- s h)
  (hash-update s h sub1))

(define (shares++ s h)
  (hash-update s h add1))

(define (ext:shares-available s h)
  (unless (shares-order? h)
    (error 'shares-available (format "Precondition: shares-order ~a\n" h)))
  (shares-available s h))

(define (shares-available s h)
  (hash-ref s h))

(define (ext:shares-available? available-s hotels)
  (unless (shares-order? available-s)
    (error 'shares-available "Precondition"))
  (shares-available? available-s hotels))

(define (shares-available? available-s hotels)
  (hash?
   (for/fold
             ((s available-s))
             ((h  (in-list hotels)))
     (and s
          (> (shares-available s h) 0)
          (shares-- s h)))))

(define (shares->list s)
  (for/fold
            ((l '()))
            ([(hotel count) (in-hash s)])
    (append (make-list count hotel) l)))

(define (list->shares hotels)
  (for/fold
            ((s  player-shares0))
            ((h  (in-list hotels)))
    (shares++ s h)))

(define ((shares-compatible s) t)
  (for/and ([(hotel count) (in-hash t)])
    (>= (shares-available s hotel) count)))

(define (string->count x)
  (define n (string->number x))
  (and n (exact-integer? n) (<= 0 n) (<= n SHARES0) n))

(define (shares->string sh)
  (string-join (for/list
                         ([(h c) (in-hash sh)])
                 (format "~a : ~a " h c))))

(define (*create-shares h n)
  (for/fold
            ((s player-shares0))
            ((i (in-range n)))
    (shares++ s h)))

(define (shares-combinable? ls)
  (define s (foldr shares-plus player-shares0 ls))
  (for/and ([(key count) (in-hash s)])
    (<= count SHARES0)))

(define (*combine-shares s)
  (foldr shares-plus player-shares0 s))

(define (ext:*combine-shares s)
  (unless (shares-combinable? s)
    (error '*combine-shares (format "Precondition error: shares-combinable ~a" s)))
  (*combine-shares s))

;; ---------------------------------------------------------------------------------------------------
;; CASH

(define CASH0 8000)

;(define-predicate cash? Cash)
(define cash? exact-nonnegative-integer?)

(define (string->cash s)
  (define n (string->number s))
  (and n (exact-integer? n) (>= n 0) n))

(define (cash->string c)
  (number->string c))

;; ---------------------------------------------------------------------------------------------------
;; the cost table for hotels, for buying shares and merging hotels 

(define PRICES
  `((Price (,WORLDWIDE ,SACKSON) (,FESTIVAL ,IMPERIAL ,AMERICAN) (,CONTINENTAL ,TOWER))
    (200            2                     0                        0)
    (300            3                     2                        0)
    (400            4                     3                        2)
    (500            5                     4                        3)
    (600            6                     5                        4)
    (700           11                     6                        5)
    (800           21                    11                        6)
    (900           31                    21                       11)
    (1000          41                    31                       21)
    (1100        +inf.0                  41                       31)
    (1200        +inf.0                 +inf.0                    41)))

(unless (set=? (apply set (apply append (rest (first PRICES)))) (apply set HOTELS))
  (define hotels:set (apply set HOTELS))
  (define hotels-in-prices (apply set (apply append (rest (first PRICES)))))
  (error 'PRICES "~a" (set-symmetric-difference hotels:set hotels-in-prices)))

;; determine the majority and minority bonus for a hotel of size tile#

(define (bonus mode hotel tile#)
  (* (or (price-per-share hotel tile#) (error 'bonus))
     (if (eq? mode 'majority) 10 5)))

;; determine the price per share for a hotel of size tile#

(define (price-per-share hotel tile#)
  (define table (rest PRICES))
  (define limit-selector
    (or
     (for/or
             ([hotels (in-list (rest (first PRICES)))]
              [selector (in-list (list second third fourth))])
       (and (member hotel hotels) selector))
     (error 'price-per-share)))
  (define price*
    (for/fold
              ([acc '()])
              ([price* (in-list table)])
      (cons (first price*) acc)))
  (define limit*
    (for/fold
              ([acc '()])
              ([price* (in-list table)])
      (cons (limit-selector price*) acc)))
  (for/fold
            ([acc #f])
            ([price (in-list price*)]
             [limit (in-list limit*)])
    (or acc (and (>= tile# limit) (assert price exact-nonnegative-integer?)))))

