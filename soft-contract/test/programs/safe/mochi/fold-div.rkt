#lang racket

(provide/contract
 [main ((-> integer?) integer? integer? . -> . real?)])

(define (foldl f z l)
  (if (empty? l) z (foldl f (f z (car l)) (cdr l))))

(define (randpos rand)
  (let ([n (rand)]) (if (> n 0) n (randpos rand))))

(define (mk-list rand n)
  (if (<= n 0) empty
      (cons (randpos rand) (mk-list rand (- n 1)))))

(define (main rand n m) (foldl / m (mk-list rand n)))
