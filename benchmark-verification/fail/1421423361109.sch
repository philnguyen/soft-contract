(module sqr racket
  (provide 
   (contract-out 
    [sqr (integer? . -> . (>/c 0))]))

  (define (sqr n)
    (* n n)))

