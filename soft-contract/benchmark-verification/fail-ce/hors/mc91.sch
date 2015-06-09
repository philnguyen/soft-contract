(module mc91 racket
  (provide/contract
   [mc91 (integer? . -> . (and/c integer? (=/c 91)))])
  (define (mc91 x)
    (if (> x 100) (- x 10)
        (mc91 (mc91 (+ x 11))))))

(require 'mc91)
(mc91 •)
