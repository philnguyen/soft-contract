#lang racket/base

;; Front-end:
;; Working with current clock

(provide;/contract
 current-clock         ;any/c]
 current-posix-seconds ;any/c]
 now/moment            ;(->i () (#:tz [tz tz/c]) [res moment?])]
 now                   ;(->i () (#:tz [tz tz/c]) [res datetime?])]
 today                 ;(->i () (#:tz [tz tz/c]) [res date?])]
 current-time          ;(->i () (#:tz [tz tz/c]) [res time?])]
 now/moment/utc        ;(-> moment?)]
 now/utc               ;(-> datetime?)]
 today/utc             ;(-> date?)]
 current-time/utc      ;(-> time?)])
 moment->iso8601
 moment->iso8601/tzid
 UTC
 moment
 moment=?
 posix->moment
)

;; -----------------------------------------------------------------------------

(require
  require-typed-check
  "gregor-structs.rkt"
)
(require (only-in "moment.rkt"
    current-timezone ;(Parameterof (U tz #f))]
    posix->moment ;(-> Exact-Rational tz Moment)]
    moment->datetime/local ;(-> Moment DateTime)]
    UTC ;String]
    moment ;(->* (Natural) (Month Natural Natural Natural Natural Natural #:tz (U tz #f) #:resolve-offset (-> (U tzgap tzoverlap) DateTime (U String #f) (U #f Moment) Moment)) Moment)]
    moment=? ;(-> Moment Moment Boolean)]
    moment->iso8601 ;(-> Moment String)]
    moment->iso8601/tzid ;(-> Moment String)]
))
(require (only-in "datetime.rkt"
    datetime->date ;(-> DateTime Date)]
    datetime->time ;(-> DateTime Time)]
))

;; =============================================================================

;(: now/moment (->* () (#:tz (U tz #f)) Moment))
(define (now/moment #:tz [tz (current-timezone)])
  (unless tz (error "current-timezone is #f"))
  (posix->moment ((current-clock)) tz))

;(: now/moment/utc (-> Moment))
(define (now/moment/utc)
  (now/moment #:tz "Etc/UTC"))

;(: now (->* () (#:tz (U tz #f)) DateTime))
(define (now #:tz [tz (current-timezone)])
  (unless tz (error "now: current-timezone is #f"))
  (moment->datetime/local (now/moment #:tz tz)))

;(: now/utc (-> DateTime))
(define (now/utc)
  (now #:tz "Etc/UTC"))

;(: today (->* () (#:tz (U tz #f)) Date))
(define (today #:tz [tz (current-timezone)])
  (unless tz (error "today: current-timezone is #f"))
  (datetime->date (now #:tz tz)))

;(: today/utc (-> Date))
(define (today/utc)
  (today #:tz "Etc/UTC"))

;(: current-time (->* () (#:tz (U tz #f)) Time))
(define (current-time #:tz [tz (current-timezone)])
  (unless tz (error "current-time:  current-timezone is #f"))
  (datetime->time (now #:tz tz)))

;(: current-time/utc (-> Time))
(define (current-time/utc)
  (current-time #:tz "Etc/UTC"))

;(: current-posix-seconds (-> Natural))
(define (current-posix-seconds)
  (let ([r (/ (inexact->exact (current-inexact-milliseconds)) 1000)])
    r))

;(: current-clock (Parameterof (-> Exact-Rational)))
(define current-clock (make-parameter current-posix-seconds))

