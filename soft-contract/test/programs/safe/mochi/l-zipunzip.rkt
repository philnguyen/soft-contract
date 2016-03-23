#lang racket
(require soft-contract/fake-contract)

(define (f g) (λ (x y) (g (+ x 1) (+ y 1))))

(define (unzip x k)
  (if (= x 0) (k 0 0)
      (unzip (- x 1) (f k))))

(define (zip x y)
  (if (= x 0)
      (if (= y 0) 0 'fail)
      (if (= y 0) 'fail
	  (+ 1 (zip (- x 1) (- y 1))))))

(define (main n)
  (unzip n zip))

(provide/contract
 [f ((integer? integer? . -> . integer?) . -> . (integer? integer? . -> . integer?))]
 [main (integer? . -> . integer?)])
