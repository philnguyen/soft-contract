#lang racket

(provide/contract
 [factorial ((and/c integer? (>=/c 0)) . -> . (and/c integer? (>=/c 1)))])

(define (factorial z)
  (if (<= z 1)
      1
      (* z (factorial (- z 1)))))
