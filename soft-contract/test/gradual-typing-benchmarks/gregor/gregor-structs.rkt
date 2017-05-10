#lang racket/base

(require
  "core-structs.rkt")

(provide
  (struct-out Date)
  (struct-out Time)
  (struct-out DateTime)
  (struct-out Moment))

;; Structs from the main gregor modules
;; `date.rkt`, `time.rkt`, `datetime.rkt`, `moment-base.rkt`

(struct Date (ymd ;: YMD]
              jdn ;: Integer]))
))

(struct Time (hmsn ;: HMSN]
              ns ;: Natural]))
))

(struct DateTime (date ;: Date]
                  time ;: Time]
                  jd ;: Exact-Rational]))
))

(struct Moment (datetime/local ;: DateTime]
                utc-offset ;: Integer]
                zone ;: (U String #f)]))
))
