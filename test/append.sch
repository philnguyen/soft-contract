(module append
  (provide
   [append ((listof any) (listof any) . -> . (listof any))])
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys)))))

(require append)
(append • •)