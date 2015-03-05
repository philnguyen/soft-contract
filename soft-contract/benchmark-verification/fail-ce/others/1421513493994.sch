(module f racket
  (provide (contract-out 
            [f (->i ([x number?]
                     [y number?])
                    [result (x y) (and/c real? (>=/c 0))])]))

  (define (f x y)
    (+ x 9)))



