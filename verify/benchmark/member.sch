(module member
  (provide
   [member (any (listof any) . -> . (listof any))])
  (define (member x l)
    (if (empty? l) empty
        (if (equal? x (car l)) l (member x (cdr l))))))

(require member)
(member • •)