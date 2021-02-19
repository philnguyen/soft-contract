#lang racket

(define (unsafe1)
  (contract integer? "4" 'me 'them))

(define (unsafe2)
  (define n "123")
  (contract exact-positive-integer? (string-append n n) 'me 'them))

(define (unsafe3)
  (contract (integer? . -> . char?) string->symbol 'me 'them))

(define str->sym* (contract (integer? . -> . char?) string->symbol 'me 'them))


(provide
 (contract-out
  [unsafe1 (-> any)]
  [unsafe2 (-> any)]

  ;; Either can be blamed:
  ;; - `them`, b/c the wrapped function is exported uncontrained
  ;; - `me`, for giving garbage to primitive `string->symbol`
  [unsafe3 (-> any)]

  ;; `them` can't be blamed given this export, b/c it always gets an opaque int from the unknown context
  [str->sym* (integer? . -> . char?)]
  ))
