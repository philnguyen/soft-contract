#lang racket/base

;; Core:
;; Year-Month-Day
;; Basic conversions

(provide;/contract
 ymd->jdn         ; (-> YMD? exact-integer?)]
 jdn->ymd         ; (-> exact-integer? YMD?)]
 jdn->wday        ; (-> exact-integer? (integer-in 0 6))]
 jdn->iso-wday    ; (-> exact-integer? (integer-in 1 7))]
 ymd->yday        ; (-> YMD? (integer-in 1 366))]
 ymd->quarter     ; (-> YMD? (integer-in 1 4))]
 ymd-add-years    ; (-> YMD? exact-integer? YMD?)]
 ymd-add-months   ; (-> YMD? exact-integer? YMD?)]
 leap-year?       ; (-> exact-integer? boolean?)]
 days-in-month    ; (-> exact-integer? (integer-in 1 12) (integer-in 28 31))]
 iso-weeks-in-year; (-> exact-integer? (or/c 52 53))]
 ;; day-of-month/c   ; any/c
)

;; -----------------------------------------------------------------------------

(require
  racket/match
  "core-structs.rkt"
  (only-in racket/math exact-truncate exact-floor))

;; =============================================================================

;; -- from `math.rkt`

;(: div (-> Integer Integer Integer))
(define (div x y)
  (define rem (remainder x y))
  (if (< (bitwise-xor rem y) 0)
      (sub1 (quotient x y))
      (quotient x y)))

;(: mod (-> Integer Integer Integer))
(define (mod x y)
  (define rem (remainder x y))
  (if (< (bitwise-xor rem y) 0)
      (+ rem y)
      rem))

;(: mod1 (-> Integer Integer Integer))
(define (mod1 x y)
  (- y (mod (- y x) y)))
;(: ymd->jdn (-> YMD Integer))
(define (ymd->jdn ymd)
  (match-define (YMD y m d) ymd)
  (let-values ([(y m) (if (< m 3)
                          (values (sub1 y) (+ m 12))
                          (values y m))])
    (+ d
       (exact-truncate
        (/ 
         (- (* 153 m) 457)
         5))
       (* 365 y)
       (exact-floor
        (/ y 4))
       (- 
        (exact-floor
         (/ y 100)))
       (exact-floor
        (/ y 400))
       1721119)))

;; -- from `ymd.rkt

;(: jdn->ymd (-> Exact-Rational YMD))
(define (jdn->ymd jdn)
  (let* ([x (exact-floor (/ (- jdn 1867216.25) 36524.25))]
         [a (+ jdn 1 x (- (exact-floor (/ x 4))))]
         [b (+ a 1524)]
         [c (exact-floor (/ (- b 122.1) 365.25))]
         [d (exact-floor (* 365.25 c))]
         [e (exact-floor (/ (- b d) 30.6001))]
         [dom (- b d (exact-floor (* 30.6001 e)))])
    (let-values ([(m y) (if (<= e 13)
                            (values (sub1 e) (- c 4716))
                            (values (- e 13) (- c 4715)))])
      (case m
        [(1) (YMD y 1 dom)]
        [(2) (YMD y 2 dom)]
        [(3) (YMD y 3 dom)]
        [(4) (YMD y 4 dom)]
        [(5) (YMD y 5 dom)]
        [(6) (YMD y 6 dom)]
        [(7) (YMD y 7 dom)]
        [(8) (YMD y 8 dom)]
        [(9) (YMD y 9 dom)]
        [(10) (YMD y 10 dom)]
        [(11) (YMD y 11 dom)]
        [(12) (YMD y 12 dom)]
        [else (error "jdn->ymd")]))))
      

;(: jdn->wday (-> Integer (U 0 1 2 3 4 5 6)))
(define (jdn->wday jdn)
  (case (mod (add1 jdn) 7)
    [(0) 0]
    [(1) 1]
    [(2) 2]
    [(3) 3]
    [(4) 4]
    [(5) 5]
    [(6) 6]
    [else (error "jdn->wday")]))

;(: jdn->iso-wday (-> Integer (U 1 2 3 4 5 6 7)))
(define (jdn->iso-wday jdn)
  (case (mod1 (jdn->wday jdn) 7)
    [(1) 1]
    [(2) 2]
    [(3) 3]
    [(4) 4]
    [(5) 5]
    [(6) 6]
    [(7) 7]
    [else (error "jdn->iso-wday")]))

;(: ymd->yday (-> YMD Natural));(integer-in 1 366)))
(define (ymd->yday ymd)
  (match-define (YMD y m d) ymd)
  (+ d
     (if (leap-year? y)
         (vector-ref CUMULATIVE-MONTH-DAYS/LEAP (sub1 m))
         (vector-ref CUMULATIVE-MONTH-DAYS (sub1 m)))))

;(: ymd->quarter (-> YMD (U 1 2 3 4)));(integer-in 1 4)))
(define (ymd->quarter ymd)
  (case (add1 (quotient (sub1 (YMD-m ymd)) 3))
    [(1) 1]
    [(2) 2]
    [(3) 3]
    [(4) 4]
    [else (error "ymd->quarter")]))

;(: ymd-add-years (-> YMD Natural YMD))
(define (ymd-add-years ymd n)
  (match-define (YMD y m d) ymd)
  (define ny (+ y n))
  (define max-dom (days-in-month ny m))
  (YMD ny m (if (<= d max-dom) d max-dom)))

;(: ymd-add-months (-> YMD Natural YMD))
(define (ymd-add-months ymd n)
  (match-define (YMD y m d) ymd)
  ;(: ny Natural)
  (define ny (+ y (div (+ m n -1) 12)))
  ;(: nm Month)
  (define nm
    (case (let ([v (mod1 (+ m n) 12)])
               (if (< v 0)
                   (+ 12 v)
                   v))
      [(1) 1]
      [(2) 2]
      [(3) 3]
      [(4) 4]
      [(5) 5]
      [(6) 6]
      [(7) 7]
      [(8) 8]
      [(9) 9]
      [(10) 10]
      [(11) 11]
      [(12) 12]
      [else (error "ymd-add-months")]))
  (define max-dom (days-in-month ny nm))
  (define nd (if (<= d max-dom) d max-dom))
  (case nm
    [(1) (YMD ny 1 nd)]
    [(2) (YMD ny 2 nd)]
    [(3) (YMD ny 3 nd)]
    [(4) (YMD ny 4 nd)]
    [(5) (YMD ny 5 nd)]
    [(6) (YMD ny 6 nd)]
    [(7) (YMD ny 7 nd)]
    [(8) (YMD ny 8 nd)]
    [(9) (YMD ny 9 nd)]
    [(10) (YMD ny 10 nd)]
    [(11) (YMD ny 11 nd)]
    [(12) (YMD ny 12 nd)]
    [else (error "ymd-add-months")]))
  

;(: leap-year? (-> Natural Boolean))
(define (leap-year? y)
  (and (zero? (remainder y 4))
       (or (not (zero? (remainder y 100)))
           (zero? (remainder y 400)))))

;(: days-in-month (-> Natural
;                     Month
;                     (U 28 29 30 31)))
(define (days-in-month y m)
  (let ([delta (if (and (= m 2)
                        (leap-year? y))
                   1
                   0)])
    (case (+ (vector-ref DAYS-PER-MONTH m) delta)
      [(28) 28]
      [(29) 29]
      [(30) 30]
      [(31) 31]
      [else (error "days in month")])))

;; (define (day-of-month/c y m)
;;   (integer-in 1 (days-in-month y m)))

;(: iso-weeks-in-year (-> Natural (U 52 53)))
(define (iso-weeks-in-year y)
  (define w (jdn->wday (ymd->jdn (YMD y 1 1))))
  
  (cond [(or (= w 4)
             (and (leap-year? y) (= w  3)))
         53]
        [else
         52]))

;(: DAYS-PER-MONTH (Vector 0 31 28 31 30 31 30 31 31 30 31 30 31))
(define DAYS-PER-MONTH
  (vector 0 31 28 31 30 31 30 31 31 30 31 30 31))

;(: CUMULATIVE-MONTH-DAYS (Vector 0 31 59 90 120 151 181 212 243 273 304 334))
(define CUMULATIVE-MONTH-DAYS
  (vector 0 31 59 90 120 151 181 212 243 273 304 334))

;(: CUMULATIVE-MONTH-DAYS/LEAP (Vector 0 31 60 91 121 152 182 213 244 274 305 335))
(define CUMULATIVE-MONTH-DAYS/LEAP
  (vector 0 31 60 91 121 152 182 213 244 274 305 335))
