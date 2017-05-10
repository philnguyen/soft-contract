#lang racket/base

;; Working with dates

(provide;/contract
 date            ;(->i ([year exact-integer?])
                 ;      ([month (integer-in 1 12)]
                 ;       [day (year month) (day-of-month/c year month)])
                 ;      [d date?])]
 date->ymd       ;(-> date? YMD?)]
 date->jdn       ;(-> date? exact-integer?)]
 ymd->date       ;(-> YMD? date?)]
 jdn->date       ;(-> exact-integer? date?)]
 date->iso-week  ;(-> date? (integer-in 1 53))]
 date->iso-wyear ;(-> date? exact-integer?)]
 date->iso8601   ;(-> date? string?)]
 date=?          ;(-> date? date? boolean?)]
 date<=?         ;(-> date? date? boolean?)]
)

;; -----------------------------------------------------------------------------

(require
  "core-structs.rkt"
  "gregor-structs.rkt"
  require-typed-check
  (only-in racket/format ~r)
  racket/match)

(require (only-in
  "ymd.rkt"
    ymd->jdn ;(-> YMD Integer)]
    jdn->ymd ;(-> Exact-Rational YMD)]
    jdn->iso-wday ;(-> Integer (U 0 1 2 3 4 5 6))]
    ymd->yday ;(-> YMD Natural)]
    iso-weeks-in-year ;(-> Natural (U 52 53))]
))

;; =============================================================================

;(: date-equal-proc (-> Date Date Boolean))
(define (date-equal-proc x y)
  (= (Date-jdn x) (Date-jdn y)))

;(: date-hash-proc (-> Date (-> Integer Integer) Integer))
(define (date-hash-proc x fn)
  (fn (Date-jdn x)))

;(: date-write-proc (-> Date Output-Port Any Void))
(define (date-write-proc d out mode)
  (fprintf out "#<date ~a>" (date->iso8601 d)))

;(: date? (-> Any Boolean))
(define date? Date?)

;(: date (->* (Natural) (Month Natural) Date))
(define (date y [m 1] [d 1])
  ;(: ymd YMD)
  (define ymd (YMD y m d))
  (Date ymd (ymd->jdn ymd)))

;(: date->ymd (-> Date YMD))
(define date->ymd Date-ymd)
;(: date->jdn (-> Any Integer))
(define (date->jdn d)
  (unless (Date? d) (error "date->jdn type error"))
  (Date-jdn d))

;(: ymd->date (-> YMD Date))
(define (ymd->date ymd)
  (match-define (YMD y m d) ymd)
  (date y m d))

;(: jdn->date (-> Exact-Rational Date))
(define (jdn->date jdn)
  (Date (jdn->ymd jdn) jdn))

;(: date->iso-week (-> Date Natural))
(define (date->iso-week d)
  (car (date->iso-week+wyear d)))

;(: date->iso-wyear (-> Date Natural))
(define (date->iso-wyear d)
  (cdr (date->iso-week+wyear d)))

;(: date->iso-week+wyear (-> Date (Pairof Natural Natural)))
(define (date->iso-week+wyear d)
  (define ymd (date->ymd d))
  (define yday (ymd->yday ymd))
  (define iso-wday (jdn->iso-wday (date->jdn d)))
  (match-define (YMD y _ _) ymd)
  (define w (quotient (+ yday (- iso-wday ) 10)
                      7))
  (cond [(zero? w)
         (define y-1 (sub1 y))
         (cons (iso-weeks-in-year y-1) y-1)]
        [(and (= w 53) (> w (iso-weeks-in-year y)))
         (cons 1 (add1 y))]
        [else
         (cons w y)]))

;(: date->iso8601 (-> Date String))
(define (date->iso8601 d)
  ;(: f (-> Integer Natural String))
  (define (f n len) (~r n #:min-width len #:pad-string "0"))
  
  (match (Date-ymd d)
    [(YMD y m d) (format "~a-~a-~a" (f y 4) (f m 2) (f d 2))]))

;(: date=? (-> Date Date Boolean))
(define (date=? d1 d2)
 (= (date->jdn d1) (date->jdn d2)))

;(: date<=? (-> Date Date Boolean))
(define (date<=? d1 d2)
  (<= (date->jdn d1) (date->jdn d2)))

