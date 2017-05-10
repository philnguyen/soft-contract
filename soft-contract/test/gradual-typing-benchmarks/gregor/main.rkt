#lang racket/base

(require
  require-typed-check
  "gregor-structs.rkt"
)

(require (only-in "date.rkt"
    date=? ;(-> Date Date Boolean)]
    date ;(->* (Natural) (Month Natural) Date)]
    date->iso8601 ;(-> Date String)]
))
(require (only-in "time.rkt"
    time=? ;(-> Time Time Boolean)]
    time->iso8601 ;(-> Time String)]
    make-time ;(->* (Integer) (Integer Integer Integer) Time)]
))
(require (only-in "datetime.rkt"
    datetime=? ;(-> DateTime DateTime Boolean)]
    datetime<=? ;(-> DateTime DateTime Boolean)]
    datetime ;(->* (Natural) (Month Natural Natural Natural Natural Natural) DateTime)]
    datetime->time ;(-> DateTime Time)]
    datetime->date ;(-> DateTime Date)]
    datetime->iso8601 ;(-> DateTime String)]
    datetime->posix ;(-> DateTime Exact-Rational)]
))
(require (only-in "moment.rkt"
    current-timezone ;(Parameterof (U tz #f))
    moment ;(->* (Natural) (Month Natural Natural Natural Natural Natural #:tz (U tz #f) #:resolve-offset (-> (U tzgap tzoverlap) DateTime (U String #f) (U #f Moment) Moment)) Moment)]
    moment=? ;(-> Moment Moment Boolean)]
    UTC ;String]
    moment->iso8601/tzid ;(-> Moment String)]
    posix->moment ;(-> Exact-Rational Moment)]
))
(require (only-in "clock.rkt"
    current-clock ;(Parameterof (-> Exact-Rational))]
    today/utc ;(-> Date)]
    today ;(->* () (#:tz (U tz #f)) Date)]
    current-time/utc ;(-> Time)]
    current-time ;(-> Time)]
    now/utc ;(-> DateTime)]
    now ;(-> DateTime)]
    now/moment/utc ;(-> Moment)]
    now/moment ;(-> Moment)]
))
(require (only-in "difference.rkt"
    datetime-months-between ;(-> DateTime DateTime Integer)]
    datetime-days-between ;(-> DateTime DateTime Integer)]
    datetime-nanoseconds-between ;(-> DateTime DateTime Integer)]
))

;; =============================================================================

;(: HISTORIC-DATES (-> (Listof DateTime)))
(define (HISTORIC-DATES)
  (list
    ;(datetime YEAR MONTH DAY HOUR MINUTE SECOND NANOSECOND)
    (datetime 2001      9  11    8     46)                   ;; 9/11 part I
    (datetime 2001      9  11    9      3)                   ;; 9/11 part II
    (datetime 1944      6   6    6      6      6          6) ;; D-Day
    (datetime 1984)
    (datetime 1963     11  22   12     30)                   ;; Kennedy
    (datetime 1865      4  14   10)                          ;; Lincoln
    (datetime 1881      7   2)                               ;; Garfield
    (datetime 1901      9   6)                               ;; McKinley
    (datetime 1933      2  15)                               ;; Roosevelt
    (datetime 1912     10  14)                               ;; Taft
    (datetime 1928     11  19)                               ;; Hoover
    (datetime 1950     11   1)                               ;; Truman
    (datetime 1835      1  30)                               ;; Jackson
    (datetime 1989     11   9)                               ;; Berlin Wall
    (datetime 1969      7  20  20      18)                   ;; Lunar landing
    (datetime 1977      8  16)                               ;; Elvis
    (datetime 1980     12   8)                               ;; Lennon
    (datetime 2013      6  18)                               ;; Kanye releases Yeezus
    (datetime 1998      9  28)                               ;; Pokemon Red released
    (datetime 1991      4  29)                               ;; Sarah bday
    (datetime 1922      2   2)                               ;; Ulysses released
    (datetime 12)
    (datetime 1030)                                          ;; Leif Erikson landing
    (datetime 1898      4)                                   ;; Spanish-American war begins
    (datetime 1099      7  10)                               ;; El Cid dies
))
(define (RANDOM-DATES)
  (list
    (datetime 324       2   1    4      32     66         23)
    (datetime   6       9  12    0      55      6          8)
    (datetime 1111     12  30    8      48     11         44)
    (datetime  32       5   8   12       2     41         39)
    (datetime  6 6 6 6 6 6 6)
    (datetime  8 6 7 5 3 0 9)
    (datetime  1251 3 18 6)
    (datetime 1386 2 1 0)
    (datetime 123 4 5 12 53)
    (datetime 2002 11 42 32)
    (datetime 777 7 77 77 77)
    (datetime  1 2 3 4 5 6 7)
    (datetime 9999     12  30   30      30     30         30)
))

;; -- tests

;(: test-clock (-> Void))
(define (test-clock)
  (parameterize ([current-clock (lambda () 1)])
   ;; -- today
   (unless (date=? (today/utc) (date 1970)) (error "test1"))
   (unless (date=? (today #:tz "America/Chicago") (date 1969 12 31)) (error "test2"))
   ;; -- current-time
   (unless (time=? (current-time/utc) (make-time 0 0 1)) (error "test 3"))
   (unless (time=? (current-time #:tz "America/Chicago") (make-time 18 0 1)) (error "test4"))
   ;; -- now
   (unless (datetime=? (now/utc) (datetime 1970 1 1 0 0 1)) (error "test5"))
   (unless (datetime=? (now #:tz "America/Chicago") (datetime 1969 12 31 18 0 1)) (error "test6"))

   ;; -- "moment"
   (unless (moment=? (now/moment/utc) (moment 1970 1 1 0 0 1 #:tz UTC)) (error "test7"))
   ;; 2015-04-25: Can't type check! Need help
   ;; (unless (moment=? (now/moment #:tz "America/Chicago")
   ;;  (moment 1969 12 31 18 0 1 0 #:tz "America/Chicago")) (error "test8"))
))

;(: test-iso (-> (Listof DateTime) Void))
(define (test-iso dates)
  (parameterize* ([current-timezone "America/New_York"]
                  [current-clock (lambda () 1463207954418177/1024000)])
   ;; -- test-case "today"
    (let ([d (today)])
     (unless (string=? "2015-04-13" (date->iso8601 d)) (error "test9")))

   ;; -- test-case "current-time"
    (let ([t (current-time)])
     (unless (string=? "04:33:37.986500977" (time->iso8601 t)) (error "test10")))

   ;; -- test-case "now"
    (let ([n (now)])
     (unless (string=? "2015-04-13T04:33:37.986500977" (datetime->iso8601 n)) (error "test11")))

   ;; -- test-case "now/moment"
    (let ([n (now/moment)])
     (unless (string=? "2015-04-13T04:33:37.986500977-04:00[America/New_York]" (moment->iso8601/tzid n)) (error "test12")))
  )
  (for ([d1 dates])
    (datetime->iso8601 d1)
    (time->iso8601 (datetime->time d1))
    (date->iso8601 (datetime->date d1)))
)

;(: test-difference (-> (Listof DateTime) Void))
(define (test-difference dates)
  (for* ([dt1 dates]
         [dt2 dates])
    (datetime<=? dt1 dt2)
    (datetime-months-between dt1 dt2)
    (datetime-days-between dt1 dt2)
    (datetime-nanoseconds-between dt1 dt2)
    (moment=?
      (posix->moment (datetime->posix dt1) UTC)
      (posix->moment (datetime->posix dt2) UTC))
    ))

;(: main (-> Natural Void))
(define (main N large?)
  (define dates
    (if large?
      (append (HISTORIC-DATES) (RANDOM-DATES))
      (HISTORIC-DATES)))
  (for ([i (in-range N)])
    (test-clock)
    (test-iso dates)
    (test-difference dates)))

;(time (main 10 #f)) ; 90ms
(time (main 10 #t)) ; 240ms
