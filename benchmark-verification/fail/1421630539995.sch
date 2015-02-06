(module f racket
  (provide (contract-out [right-triangle? (-> integer? integer? integer?)]))
  
  (define (right-triangle? a b c)
  (= (expt c 2) (+ (expt a 2) (expt b 2))))

  
)
