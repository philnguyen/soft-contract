(module f racket
  (provide (contract-out 
            [f (-> number? number? real?)]))

  (define (f x y)
    (+ x 9)))



