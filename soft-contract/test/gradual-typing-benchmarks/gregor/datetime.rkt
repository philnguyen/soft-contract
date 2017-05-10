#lang racket/base

;; Working with DateTime objects
;; (i.e. dates and times at the same time)

(require
  require-typed-check
  racket/match
  "core-structs.rkt"
  "gregor-structs.rkt"
  (only-in racket/math exact-round exact-floor))

(require (only-in
  "hmsn.rkt"
    NS/DAY ;Natural]
    NS/SECOND ;Natural]
))
(require (only-in
  "date.rkt"
    date->iso8601 ;(-> Date String)]
    date->jdn ;(-> Any Integer)]
    jdn->date ;(-> Exact-Rational Date)]
    date->ymd ;(-> Date YMD)]
    date ;(->* (Natural) (Month Natural) Date)]
    date=? ;(-> Date Date Boolean)]
))
(require (only-in "time.rkt"
    time->iso8601 ;(-> Time String)]
    time->ns ;(-> Any Natural)]
    day-ns->time ;(-> Natural Time)]
    make-time ;(->* (Integer) (Integer Integer Integer) Time)]
    time=? ;(-> Time Time Boolean)]
))

;; -----------------------------------------------------------------------------

(provide;/contract
 datetime                 ;(->i ([year exact-integer?])
                          ;      ([month (integer-in 1 12)]
                          ;       [day (year month) (day-of-month/c year month)]
                          ;       [hour (integer-in 0 23)]
                          ;       [minute (integer-in 0 59)]
                          ;       [second (integer-in 0 59)]
                          ;       [nanosecond (integer-in 0 (sub1 NS/SECOND))])
                          ;      [dt datetime?])]
 datetime->date           ;(-> datetime? date?)]
 datetime->time           ;(-> datetime? time?)]
 datetime->jd             ;(-> datetime? rational?)]
 datetime->posix          ;(-> datetime? rational?)]
 date+time->datetime      ;(-> date? time? datetime?)]
 jd->datetime             ;(-> real? datetime?)]
 posix->datetime          ;(-> real? datetime?)]
 datetime->iso8601        ;(-> datetime? string?)]
 datetime-add-nanoseconds ;(-> datetime? exact-integer? datetime?)]
 datetime-add-seconds     ;(-> datetime? exact-integer? datetime?)]
 datetime=?               ;(-> datetime? datetime? boolean?)]
 datetime<?               ;(-> datetime? datetime? boolean?)]
 datetime<=?              ;(-> datetime? datetime? boolean?)]
)

;; =============================================================================

;(: datetime-equal-proc (-> DateTime DateTime Boolean))
(define (datetime-equal-proc x y)
  (= (datetime->jd x)
     (datetime->jd y)))

;(: datetime-hash-proc (-> DateTime (-> Exact-Rational Integer) Integer))
(define (datetime-hash-proc x fn)
  (fn (datetime->jd x)))

;(: datetime-write-proc (-> DateTime Output-Port Any Void))
(define (datetime-write-proc dt out mode)
  (fprintf out "#<datetime ~a>" (datetime->iso8601 dt)))

;(: datetime? (-> Any Boolean))
(define datetime? DateTime?)

;(: datetime->date (-> DateTime Date))
(define datetime->date DateTime-date)
;(: datetime->time (-> DateTime Time))
(define datetime->time DateTime-time)
;(: datetime->jd (-> Any Exact-Rational))
(define (datetime->jd d)
  (unless (DateTime? d) (error "datetime->jd type error"))
  (DateTime-jd d))

;(: datetime->posix (-> DateTime Exact-Rational))
(define (datetime->posix dt)
  (jd->posix (datetime->jd dt)))

;(: posix->datetime (-> Exact-Rational DateTime))
(define (posix->datetime posix)
  (jd->datetime (posix->jd (inexact->exact posix))))

;(: date+time->datetime (-> Date Time DateTime))
(define (date+time->datetime d t)
  (DateTime d t (date+time->jd d t)))

;(: jd->datetime (-> Real DateTime))
(define (jd->datetime jd)
  (define ejd (inexact->exact jd))
  (define-values (d t) (jd->date+time ejd))
  (date+time->datetime d t))

;(: datetime (->* (Natural) (Month Natural Natural Natural Natural Natural) DateTime))
(define (datetime year [month 1] [day 1] [hour 0] [minute 0] [second 0] [nano 0])
  (date+time->datetime (date year month day)
                       (make-time hour minute second nano)))

;(: datetime->iso8601 (-> DateTime String))
(define (datetime->iso8601 dt)
  (format "~aT~a"
          (date->iso8601 (datetime->date dt))
          (time->iso8601 (datetime->time dt))))

;(: datetime=? (-> DateTime DateTime Boolean))
(define (datetime=? dt1 dt2)
  (= (datetime->jd dt1) (datetime->jd dt2)))

;(: datetime<? (-> DateTime DateTime Boolean))
(define (datetime<? dt1 dt2)
  (< (datetime->jd dt1) (datetime->jd dt2)))

;(: datetime<=? (-> DateTime DateTime Boolean))
(define (datetime<=? dt1 dt2)
  (<= (datetime->jd dt1) (datetime->jd dt2)))

;(: date+time->jd (-> Date Time Exact-Rational))
(define (date+time->jd d t)
  (define jdn    (date->jdn d))
  (define day-ns (time->ns t))

  (+ (- jdn 1/2)
     (/ day-ns NS/DAY)))

;(: jd->date+time (-> Exact-Rational (Values Date Time)))
(define (jd->date+time jd)
  (define jdn    (jd->jdn jd))
  (define d      (jdn->date jdn))
  (define day-ns (jd->day-ns jd))
  (define t      (day-ns->time day-ns))

  (values d t))

;(: jd->jdn (-> Exact-Rational Exact-Rational))
(define (jd->jdn jd)
  (define lo (exact-floor jd))

  ;; math-class rounding: round up for >= 1/2
  (if (>= (- jd lo) 1/2)
      (add1 lo)
      lo))

;(: jd->day-ns (-> Exact-Rational Natural))
(define (jd->day-ns jd)
  (define base (- jd 1/2))
  (define frac (- base (exact-floor base)))
  (define r (exact-round (* frac NS/DAY)))
  r)

;(: jd->posix (-> Exact-Rational Exact-Rational))
(define (jd->posix jd)
  (* 86400 (- jd (+ 2440587 1/2))))

;(: posix->jd (-> Exact-Rational Exact-Rational))
(define (posix->jd posix)
  (+ (/ posix 86400) (+ 2440587 1/2)))

;(: datetime-add-nanoseconds (-> DateTime Integer DateTime))
(define (datetime-add-nanoseconds dt n)
  (jd->datetime
   (+ (datetime->jd dt)
      (/ n NS/DAY))))

;(: datetime-add-seconds (-> DateTime Integer DateTime))
(define (datetime-add-seconds dt n)
  (datetime-add-nanoseconds dt (* n NS/SECOND)))

