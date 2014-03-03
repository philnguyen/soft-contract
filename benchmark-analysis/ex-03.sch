(module lib
  (provide [member (any (listof any) . -> . (or/c false? (nelistof any)))]))
(module ex-03
  (provide [f (any (listof any) . -> . false?)])
  (require lib)
  (define (f v l)
    (let ([x (member v l)])
      (if x (false? f) #f))))
(require ex-03 lib)
(f • •)