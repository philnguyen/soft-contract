#lang racket/base

;; Core:
;; Essential structs

(provide
 (struct-out YMD)
 (struct-out HMSN)
)

;; TODO precise types for year, day, hour, second?
;; (the others are not feasible)

(struct YMD (y ;: Natural]
             m ;: Month]
             d ;: Natural])
)#:transparent)
(struct HMSN (h ;: Integer]
              m ;: Integer]
              s ;: Integer]
              n ;: Integer])
) #:transparent)
