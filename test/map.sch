(module map
  (provide
   [map ((any . -> . any) (listof any) . -> . (listof any))])
  (define (map f xs)
    (if (empty? xs) empty
        (cons (f (car xs)) (map f (cdr xs))))))

(require map)
(map • •)