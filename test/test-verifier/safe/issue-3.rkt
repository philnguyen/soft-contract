(module m racket
  (provide
   (contract-out
    [id (->i ([x any/c]) (res (x) (λ (a) (equal? a x))))]))
  (define (id x) x))
