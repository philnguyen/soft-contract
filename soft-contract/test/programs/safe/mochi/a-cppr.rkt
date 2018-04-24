#lang racket

(define ((make-array n) i)
  (unless (and (<= 0 i) (< i n))
    (error 'boom))
  0)

(define (update i n des x)
  (λ (j) (if (= i j) x (des i))))

(define (f m src des)
  (define (bcopy m src des i)
    (if (>= i m)
        des
        (let ([des (update i m des (src i))])
          (bcopy m src des (+ i 1)))))
  (define (print-array m array i)
    (when (< i m)
      (print-array m array (+ i 1))))
  (define array (bcopy m src des 0))
  (print-array m array 0))

(define (main n)
  (let ([array1 (make-array n)]
        [array2 (make-array n)])
    (when (> n 0)
      (f n array1 array2))))
