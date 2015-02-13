(module f racket
  (provide (contract-out 
            [f (->i ([x number?]
                     [y number?])
                    [result (x y) real?])]))

  (define (f x y)
    (+ x 9)))



