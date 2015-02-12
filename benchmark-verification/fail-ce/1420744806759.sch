(module foo racket
  (provide (contract-out [foo (integer? . -> . (or/c string? integer?))]))
  (define (foo n)
    (if (< 10 n) "hello" (if (> 5 n) #t 5))))
