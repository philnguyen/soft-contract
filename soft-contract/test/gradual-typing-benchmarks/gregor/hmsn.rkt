#lang racket/base

;; Core:
;; Hours, Minutes, Seconds, Nanoseconds
;; constants and conversions

(provide
 NS/MICRO
 NS/MILLI
 NS/SECOND
 NS/MINUTE
 NS/HOUR
 NS/DAY
 MILLI/DAY
 hmsn->day-ns
 day-ns->hmsn)

(require
  "core-structs.rkt"
  racket/match)

;; =============================================================================

;(: NS/SECOND Natural)
(define NS/SECOND 1000000000)
;(: NS/MILLI Natural)
(define NS/MILLI 1000000)
;; (define NS/MILLI (/ NS/SECOND 1000))
;(: NS/MICRO Natural)
(define NS/MICRO 1000)
;; (define NS/MICRO (/ NS/MILLI 1000))
;(: NS/MINUTE Natural)
(define NS/MINUTE (* NS/SECOND 60))
;(: NS/HOUR Natural)
(define NS/HOUR (* NS/MINUTE 60))
;(: NS/DAY Natural)
(define NS/DAY (* 86400 NS/SECOND))
;(: MILLI/DAY Natural)
(define MILLI/DAY 86400000)
;; (define MILLI/DAY (/ NS/DAY NS/MILLI))
;(: DAYS/NS Exact-Rational)
(define DAYS/NS (/ 1 NS/DAY))

;; (define day-ns/c (integer-in 0 (sub1 NS/DAY)))
;; Codomain of hmsn->day-ns should be a day-ns/c
;(: hmsn->day-ns (-> HMSN Natural))
(define (hmsn->day-ns hmsn)
  (match-define (HMSN h m s n) hmsn)
  (define r (+ (* NS/HOUR h)
               (* NS/MINUTE m)
               (* NS/SECOND s)
               n))
  r)

;(: day-ns->hmsn (-> Natural HMSN))
(define (day-ns->hmsn ns)
  (let* ([h (quotient ns NS/HOUR)]
         [ns (- ns (* h NS/HOUR))]
         [m (quotient ns NS/MINUTE)]
         [ns (- ns (* m NS/MINUTE))]
         [s (quotient ns NS/SECOND)]
         [ns (- ns (* s NS/SECOND))])
    (HMSN h m s ns)))
