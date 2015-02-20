#lang racket
(require soft-contract/fake-contract)

(define (nth n xs)
  (if (= n 0) (car xs) (nth (- n 1) (cdr xs))))

(define (mk-list n)
  (if (< n 0) empty
      (cons n (mk-list (- n 1)))))

(define (main n)
  (let ([xs (mk-list n)])
    (if (empty? xs) 0 (nth 0 xs))))

(provide/contract
 [nth (integer? (listof integer?) . -> . integer?)]
 [mk-list (integer? . -> . (listof integer?))]
 [main (integer? . -> . integer?)])
