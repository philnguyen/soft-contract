#lang racket

(provide/contract
 [f (((-> void?) . -> . void?) integer? . -> . any/c)])

(define (f g n)
  (define inc! (λ () (set! n (+ 1 n))))
  (if (= n 0) 1 (/ 1 n)) ; 1/n unreachable
  (g inc!)
  (if (= n 0) 1 (/ 2 n)) ; 2/n unreachable despite `inc!` escaped
  (define m n)
  (if (= m 0) 1 (/ 3 m)) ; 3/m unreachable
  )
