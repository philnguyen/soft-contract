(module lib
  (provide [member (any/c (listof any/c) . -> . (or/c false? (nelistof any/c)))]))
(module ex-03
  (provide [f (any/c (listof any/c) . -> . false?)])
  (require lib)
  (define (f v l)
    (let ([x (member v l)])
      (if x (false? f) #f))))
(require ex-03 lib)
(f • •)
