#lang racket

(define (tak x y z)
  (if (not (< y x))
      z
      (tak (tak (- x 1) y z)
           (tak (- y 1) z x)
           (tak (- z 1) x y))))

(provide
 (contract-out
  [tak (integer? integer? integer? . -> . integer?)]))
