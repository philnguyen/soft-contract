#lang racket

(define (weird-equal? x y)
  (cond [(and (number? x) (number? y)) (= x y)]
        [(and (string? x) (string? y)) (string=? x y)]))

(provide/contract
 [weird-equal?
  (->i ([x (or/c string? number?)]
        [y (x) (if (string? x) string? number?)])
       (_ boolean?))
  ;; conceptually this, but below contract won't work
  ;; (case->
  ;;   [number? number? . -> . boolean?]
  ;;   [string? string? . -> . boolean?])
  ])
