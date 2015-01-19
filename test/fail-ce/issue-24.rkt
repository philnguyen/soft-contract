(module foo racket
  (provide (contract-out [foo (real? . -> . (not/c (=/c 1)))]))
  (define (foo s)
    (* s 3)))
