(module f racket
  (provide (contract-out [pow (-> integer? integer?)]))
  
  (define (pow a b)
    (expt a b))

  
)
