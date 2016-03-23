#lang racket
(require soft-contract/fake-contract)

(define (mk-list n)
  (if (<= n 0) empty
      (cons (λ (m) (+ m n)) (mk-list (- n 1)))))
(define (foldr f z xs)
  (if (empty? xs) z (f (car xs) (foldr f z (cdr xs)))))
(define (compose f g) (λ (x) (f (g x))))
(define (main n)
  (let ([xs (mk-list n)])
    (foldr compose (λ (x) x) xs)))

(provide/contract
   [mk-list (integer? . -> . (listof (integer? . -> . integer?)))]
   [foldr (((integer? . -> . integer?) (integer? . -> . integer?) . -> . (integer? . -> . integer?))
           (integer? . -> . integer?)
           (listof (integer? . -> . integer?))
           . -> . (integer? . -> . integer?))]
   [main (->i ([n integer?])
	      (res (n) (and/c (integer? . -> . integer?) (λ (f) (>= (f 0) 0)))))])
