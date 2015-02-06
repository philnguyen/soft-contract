(module f racket
  (provide (contract-out [f (-> (listof integer?) integer?)]))
  (define (f n)
    (/ 1 (- 100 n))))
