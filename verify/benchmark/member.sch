(module member racket
  (provide/contract
   [member (any/c (listof any/c) . -> . (listof any/c))])
  (define (member x l)
    (if (empty? l) empty
        (if (equal? x (car l)) l (member x (cdr l))))))

(require 'member)
(member • •)
