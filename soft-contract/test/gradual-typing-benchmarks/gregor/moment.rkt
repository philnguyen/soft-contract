#lang racket/base

;; Moments in time

(require
  require-typed-check
  racket/match
  "gregor-structs.rkt"
  (only-in racket/math exact-round)
)
(require (only-in "../base/tzinfo/main.rkt"
  system-tzid ;(-> (U tz #f))]
  tzoffset tzoffset? tzoffset-utc-seconds
  local-seconds->tzoffset ;(-> String Integer (U tzoffset tzgap tzoverlap))]
  utc-seconds->tzoffset ;(-> String Exact-Rational tzoffset)]
))
(require (only-in "hmsn.rkt"
    NS/SECOND ;Natural]
))
(require (only-in "datetime.rkt"
    datetime ;(->* (Natural) (Month Natural Natural Natural Natural Natural) DateTime)]
    datetime->posix ;(-> DateTime Exact-Rational)]
    posix->datetime ;(-> Exact-Rational DateTime)]
    datetime->jd ;(-> DateTime Exact-Rational)]
    datetime-add-seconds ;(-> DateTime Integer DateTime)]
))
(require (only-in "moment-base.rkt"
    make-moment ;(-> DateTime Integer (U String #f) Moment)]
    moment->iso8601 ;(-> Moment String)]
    moment->iso8601/tzid ;(-> Moment String)]
))
(require (only-in "offset-resolvers.rkt"
    resolve-offset/raise ;(-> (U tzgap tzoverlap) DateTime (U String #f) (U Moment #f) Moment)]
))

;; -----------------------------------------------------------------------------

(provide;/contract
 current-timezone       ;(parameter/c tz/c)]
 moment                 ;(->i ([year exact-integer?])
                        ;      ([month (integer-in 1 12)]
                        ;       [day (year month) (day-of-month/c year month)]
                        ;       [hour (integer-in 0 23)]
                        ;       [minute (integer-in 0 59)]
                        ;       [second (integer-in 0 59)]
                        ;       [nanosecond (integer-in 0 (sub1 NS/SECOND))]
                        ;       #:tz [tz tz/c]
                        ;       #:resolve-offset [resolve offset-resolver/c])
                        ;      [res moment?])]
 datetime+tz->moment    ;(-> datetime? tz/c offset-resolver/c moment?)]
 moment->iso8601        ;(-> moment? string?)]
 moment->iso8601/tzid   ;(-> moment? string?)]
 moment->datetime/local ;(-> moment? datetime?)]
 moment->utc-offset     ;(-> moment? exact-integer?)]
 moment->timezone       ;(-> moment? tz/c)]
 moment->tzid           ;(-> moment? (or/c string? #f))]
 moment->jd             ;(-> moment? rational?)]
 moment->posix          ;(-> moment? rational?)]
 posix->moment          ;(-> rational? tz/c moment?)]
 moment-add-nanoseconds ;(-> moment? exact-integer? moment?)]
 moment-in-utc          ;(-> moment? moment?)]
 timezone-adjust        ;(-> moment? tz/c moment?)]
 timezone-coerce        ;(->i ([m moment?]
                        ;       [z tz/c])
                        ;      (#:resolve-offset [r offset-resolver/c])
                        ;      [res moment?])]
 moment=?               ;(-> moment? moment? boolean?)]
 moment<?               ;(-> moment? moment? boolean?)]
 moment<=?              ;(-> moment? moment? boolean?)]
 UTC                    ;tz/c]
)

;; =============================================================================

;(: current-timezone (Parameterof (U tz #f)))
(define current-timezone (make-parameter (system-tzid)))

;(: moment (->* (Natural) (Month
;                          Natural Natural Natural Natural Natural
;                          #:tz (U tz #f)
;                          #:resolve-offset (-> (U tzgap tzoverlap)
;                                               DateTime
;                                               (U String #f)
;                                               (U #f Moment) Moment)
;                          )
;                          Moment))
(define (moment year [month 1] [day 1] [hour 0] [minute 0] [second 0] [nano 0]
                #:tz [tz (current-timezone)]
                #:resolve-offset [resolve resolve-offset/raise])
  (when (eq? tz #f) (error "no timezone"))
  (datetime+tz->moment (datetime year month day hour minute second nano) tz resolve))

;(: datetime+tz->moment (-> DateTime
;                           (U Integer String)
;                           (-> (U tzgap tzoverlap)
;                               DateTime
;                               (U String #f)
;                               (U Moment #f) Moment)
;                           Moment))
(define (datetime+tz->moment dt zone resolve)
  (cond [(string? zone)
         (define res (local-seconds->tzoffset zone (exact-round (datetime->posix dt))))
         (cond
          [(tzoffset? res)
           (make-moment dt (tzoffset-utc-seconds res) zone)]
          [else (resolve res dt zone #f)])]
        [else
         (make-moment dt zone #f)]))

(define moment->datetime/local Moment-datetime/local)
(define moment->utc-offset     Moment-utc-offset)
(define moment->tzid           Moment-zone)

;(: moment->timezone (-> Moment tz))
(define (moment->timezone m)
  (or (moment->tzid m)
      (moment->utc-offset m)))

;(: moment-in-utc (-> Moment Moment))
(define (moment-in-utc m)
  (if (equal? UTC (moment->timezone m))
      m
      (timezone-adjust m UTC)))

;(: moment->jd (-> Any Exact-Rational))
(define (moment->jd m)
  (unless (Moment? m) (error "moment->jd type error"))
  (datetime->jd
   (moment->datetime/local
    (moment-in-utc m))))

;(: moment->posix (-> Moment Exact-Rational))
(define (moment->posix m)
  (datetime->posix
   (moment->datetime/local
    (moment-in-utc m))))

;(: posix->moment (-> Exact-Rational tz Moment))
(define (posix->moment p z)
  ;(: off Integer)
  (define off
    (cond [(string? z) (tzoffset-utc-seconds (utc-seconds->tzoffset z p))]
          [else        0]))
  (define dt (posix->datetime (+ p off)))
  (unless (string? z) (error "posix->moment: can't call make-moment with an integer"))
  (make-moment dt off z))

;(: moment-add-nanoseconds (-> Moment Natural Moment))
(define (moment-add-nanoseconds m n)
  (posix->moment (+ (moment->posix m) (* n (/ 1 NS/SECOND)))
                 (moment->timezone m)))

;(: timezone-adjust (-> Moment (U Natural String) Moment))
(define (timezone-adjust m z)
  (match-define (Moment dt neg-sec _) m)
  ;(: dt/utc DateTime)
  (define dt/utc
    (datetime-add-seconds dt (- neg-sec)))
  (cond [(string? z)
         (define posix (datetime->posix dt/utc))
         (match-define (tzoffset offset _ _) (utc-seconds->tzoffset z posix))
         (define local (datetime-add-seconds dt/utc offset))
         (make-moment local offset z)]
        [else
         (define local (datetime-add-seconds dt/utc z))
         (make-moment local z #f)]))

;(: timezone-coerce (->* [Moment (U Natural String)]
;                        (#:resolve-offset (-> (U tzgap tzoverlap) DateTime (U String #f) (U #f Moment) Moment))
;                        Moment))
(define (timezone-coerce m z #:resolve-offset [resolve resolve-offset/raise])
  (datetime+tz->moment (moment->datetime/local m) z resolve))

;(: moment=? (-> Moment Moment Boolean))
(define (moment=? m1 m2)
  (= (moment->jd m1) (moment->jd m2)))

;(: moment<? (-> Moment Moment Boolean))
(define (moment<? m1 m2)
  (< (moment->jd m1) (moment->jd m2)))

;(: moment<=? (-> Moment Moment Boolean))
(define (moment<=? m1 m2)
  (<= (moment->jd m1) (moment->jd m2)))

;(: UTC String)
(define UTC "Etc/UTC")

