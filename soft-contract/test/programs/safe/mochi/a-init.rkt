#lang racket

(define ((make-array n) i)
  (unless (and (<= 0 i) (< i n))
    (error 'boom))
  0)

(define ((update i a x) j)
  (if (and (> j (- i 1)) (<= j i))
      x
      (a j)))

(define (init i n a)
  (if (>= i n)
      a
      (init (+ i 1) n (update i a 1))))

(define (main k n i)
  (when (and (>= k 0) (<= k 0))
    (let ([x (init k n (make-array n))])
      (when (and (<= 0 i) (< i n))
        (unless (>= (x i) 1)
          (error 'boom))))))
