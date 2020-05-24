#lang racket

(define/contract f
  ((number? . -> . real?) . -> . (string . -> . string?))
  (λ (on-num)
    (λ (s)
      (cond [(string->number s) => (λ (n) (number->string (on-num n)))]
            [else ""]))))

(define/contract str-inc string? ((f values) "42"))
