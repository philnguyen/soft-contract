(module f racket
  (provide/contract
    [f ((one-of/c 99) . -> . integer?)])

  (define (f n)
    (if (= n 100)
        5
        (/ 1 (- 100 n)))))
