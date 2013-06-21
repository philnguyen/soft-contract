(module map-append
  (provide
   [map-append ((any . -> . (listof any)) (listof any) . -> . (listof any))]
   [append ((listof any) (listof any) . -> . (listof any))])
  
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys))))
  
  (define (map-append f xs)
    (if (empty? xs) empty
        (append (f (car xs)) (map-append f (cdr xs))))))

(require map-append)
(map-append • •)