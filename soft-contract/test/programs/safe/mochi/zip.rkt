#lang racket
(require soft-contract/fake-contract)

(define (zip xs ys) ; zip itself is unsafe
  (cond
   [(and (empty? xs) (empty? ys)) empty]
   [(and (cons? xs) (cons? ys)) (cons (cons (car xs) (car ys)) (zip (cdr xs) (cdr ys)))]
   [else 'fail]))

(define (mk-list n)
  (if (< n 0) empty (cons n (mk-list (- n 1)))))

(define (main n)
  (let ([xs (mk-list n)]) (zip xs xs)))

(provide/contract
 [mk-list (integer? . -> . (listof integer?))]
 [main (integer? . -> . (listof (cons/c integer? integer?)))])
