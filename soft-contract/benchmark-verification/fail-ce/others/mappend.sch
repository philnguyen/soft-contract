(module map-append racket
  (provide/contract
   [map-append ((any/c . -> . (listof any/c)) any/c . -> . (listof any/c))]
   [append ((listof any/c) (listof any/c) . -> . (listof any/c))])
  
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys))))
  
  (define (map-append f xs)
    (if (empty? xs) empty
        (append (f (car xs)) (map-append f (cdr xs))))))

(require 'map-append)
(map-append • •)
