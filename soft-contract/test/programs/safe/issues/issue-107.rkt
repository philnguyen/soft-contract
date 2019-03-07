#lang racket

(define (f x y)
  (if (zero? y)
    (error 'die)
    (/ (sum x) y)))

(define (sum x)
  (apply + x))

(provide (contract-out
  (sum (-> (listof real?) real?))
  (f (-> (listof real?) real? real?))))
