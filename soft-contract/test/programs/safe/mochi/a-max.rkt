#lang racket

(define ((make-array n) i) (- n i))

(define (array-max n i a m)
  (if (>= i n)
      m
      (let* ([x (a i)]
             [z (if (> x m) x m)])
        (array-max n (+ i 1) a z))))

(define (main n i)
  (when (and (> n 0) (>= i 0) (<= i 0))
    (let ([m (array-max n i (make-array n) -1)])
      (unless (>= m n)
        (error 'boom)))))
