(module factorial racket
  (provide/contract
   [factorial (([x integer?]) . ->i . (res (x) (and/c integer? (>/c 1))))])
  (define (factorial n)
    (if (zero? n) 1 (* n (factorial (sub1 n))))))

(require 'factorial)
(factorial •)
