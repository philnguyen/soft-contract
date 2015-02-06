(module f racket
  (provide (contract-out [f (-> (listof integer?) integer?)]))
  (define (f n)
    (if (null? n) 1
    (/ 1 (- 100 (- 1 (car n)))))))
