(module lib racket
  (provide/contract [member (any/c (listof any/c) . -> . (or/c false? (nelistof any/c)))]))
(module ex-03 racket
  (provide/contract [f (any/c (listof any/c) . -> . false?)])
  (require (submod ".." lib))
  (define (f v l)
    (let ([x (member v l)])
      (if x (false? f) #f))))
(require 'ex-03 'lib)
(f • •)
