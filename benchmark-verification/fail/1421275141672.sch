(module m1 racket
  (define (f x) x)
  (define c any/c)
  (define i integer?)
  (provide (contract-out [f (-> c i)])))
