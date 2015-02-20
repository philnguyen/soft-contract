#lang racket
(require soft-contract/fake-contract)

(define (factorial n)
  (factorial-acc n 1))

(define (factorial-acc n acc)
  (if (zero? n) acc
      (factorial-acc (sub1 n) (* n acc))))

(provide/contract
 [factorial (integer? . -> . integer?)])
