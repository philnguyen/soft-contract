(module append
  (provide
   [append ((listof any/c) (listof any/c) . -> . (listof any/c))])
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys)))))

(require append)
(append • •)
