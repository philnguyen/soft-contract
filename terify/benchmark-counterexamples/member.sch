(module member
  (provide
   [member (any (listof any) . -> . #|HERE|# bool?)])
  (define (member x l)
    (cond
     [(empty? l) empty]
     [(equal? x (car l)) l]
     [else (member x (cdr l))])))

(require member)
(member • •)
