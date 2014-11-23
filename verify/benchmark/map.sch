(module map
  (provide
   [map ([_ : (any . -> . any)] [l : (listof any)] . -> .
                                (and/c (listof any)
                                       (λ (r) (equal? (empty? l) (empty? r)))))])
  (define (map f xs)
    (if (empty? xs) empty
        (cons (f (car xs)) (map f (cdr xs))))))

(require map)
(map • •)