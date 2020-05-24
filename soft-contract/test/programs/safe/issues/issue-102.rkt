#lang racket

(define (deep n)
  (if (zero? n) n (list (deep (- n 1)))))

(define my-ctc
  (or/c exact-nonnegative-integer?
        (list/c (recursive-contract my-ctc #:chaperone))))

(provide
  (contract-out
    (deep (-> exact-nonnegative-integer? my-ctc))))
