(module append racket
  (provide/contract
   [append ((listof any/c) (listof any/c) . -> . #|HERE|# cons?)])
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys)))))

(require 'append)
(append • •)
