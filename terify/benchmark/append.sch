(module append
  (provide
   [append ((listof any) (listof any) . -> . #|HERE|#(nelistof any))])
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys)))))

(require append)
(append • •)
