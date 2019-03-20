#lang racket

(define/contract f
  ((number? . -> . number?) . -> . (string . -> . string?))
  (λ (on-num)
    (λ (s)
      (cond [(string->number s) => (λ (n) (number->string (on-num n)))]
            [else ""]))))

(define/contract str-inc string? ((f values) "42"))

