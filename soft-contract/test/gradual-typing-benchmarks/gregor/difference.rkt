#lang racket/base

;; Time deltas

(provide;/contract
 datetime-months-between      ;(-> datetime? datetime? exact-integer?)]
 datetime-days-between        ;(-> datetime? datetime? exact-integer?)]
 datetime-nanoseconds-between ;(-> datetime? datetime? exact-integer?)])
)

;; -----------------------------------------------------------------------------

(require
  require-typed-check
  racket/match
  "core-structs.rkt"
  "gregor-structs.rkt"
  (only-in racket/math exact-floor))
(require (only-in
  "ymd.rkt"
    days-in-month ;(-> Natural Month (U 28 29 30 31))]
  ))
(require (only-in "hmsn.rkt"
    NS/DAY ;Natural]
))
(require (only-in "date.rkt"
    date->ymd ;(-> Date YMD)]
    date ;(->* (Natural) (Month Natural) Date)]
))
(require (only-in "datetime.rkt"
    datetime<? ;(-> Any Any Boolean)]
    datetime->date ;(-> DateTime Date)]
    date+time->datetime ;(-> Date Time DateTime)]
    datetime->time ;(-> DateTime Time)]
    datetime->jd ;(-> DateTime Exact-Rational)]
    datetime ;(->* (Natural) (Month Natural Natural Natural Natural Natural) DateTime)]
))

;; =============================================================================

;; difference
;(: datetime-months-between (-> DateTime DateTime Integer))
(define (datetime-months-between dt1 dt2)
  (cond [(datetime<? dt2 dt1)
         (- (datetime-months-between dt2 dt1))]
        [else
         ;(: d1 Date)
         (define d1 (datetime->date dt1))
         ;(: d2 Date)
         (define d2 (datetime->date dt2))

         (match* ((date->ymd d1) (date->ymd d2))
           [((YMD y1 m1 d1) (YMD y2 m2 d2))
            ;(: diff Integer)
            (define diff
              (+ (* (- y2 y1) 12)
                 m2
                 (- m1)))
            ;(: start-dom Natural)
            (define start-dom
              (let ([r (if (and (> d1 d2)
                       (= (days-in-month y2 m2) d2))
                  d2
                  d1)])
                (abs r)))
            ;(: dt1a DateTime)
            (define dt1a (date+time->datetime (date y1 m1 start-dom) (datetime->time dt1)))

            (define ts1 (- (datetime->jd dt1a) (datetime->jd (datetime y1 m1))))
            (define ts2 (- (datetime->jd dt2)  (datetime->jd (datetime y2 m2))))
            (if (< ts2 ts1)
                (sub1 diff)
                diff)])]))

;(: datetime-days-between (-> DateTime DateTime Integer))
(define (datetime-days-between dt1 dt2)
  (exact-floor (- (datetime->jd dt2) (datetime->jd dt1))))

;(: datetime-nanoseconds-between (-> DateTime DateTime Integer))
(define (datetime-nanoseconds-between dt1 dt2)
  (- (datetime->jdns dt2)
     (datetime->jdns dt1)))

;(: datetime->jdns (-> DateTime Integer))
(define (datetime->jdns dt)
  (exact-floor (* (datetime->jd dt) NS/DAY)))
