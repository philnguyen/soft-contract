(module mc91 racket
  (provide/contract
   [mc91 (([n integer?]) . ->i . (res (n) (and/c integer? (λ (a) (if (<= n 101) (= a 91) #t)))))])
  (define (mc91 x)
    (if (> x 100) (- x 10)
        (mc91 (mc91 (+ x 11))))))

(require 'mc91)
(mc91 •)
