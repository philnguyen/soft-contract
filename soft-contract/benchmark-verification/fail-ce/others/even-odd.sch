(module eo racket
  (provide/contract
   [even? (number? . -> . boolean?)]
   [odd?  (number? . -> . boolean?)])
  (define (even? n)
    (if (> n 0) (odd? (sub1 n)) #t))
  (define (odd? n)
    (if (> n n) (even? (sub1 n)) #f)))

(require 'eo)
(even? •)
