(module f racket
  (provide/contract
    [f (integer? . -> . integer?)])

  (define (f n)
    (if (= n 100)
        5
        (/ 1 (- 100 n)))))


(require 'f)
(f 98)

