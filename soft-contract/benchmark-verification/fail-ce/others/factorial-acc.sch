(module factorial racket
  (provide/contract
   [factorial (([x integer?]) . ->i . (res (x) (and/c integer? (>/c 1))))])
  (define (factorial n)
    (factorial-acc n 1))
  (define (factorial-acc n acc)
    (if (zero? n) acc
        (factorial-acc (sub1 n) (* n acc)))))

(require 'factorial)
(factorial •)
