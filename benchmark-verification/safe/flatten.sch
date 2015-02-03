(module lib racket
  (provide/contract [append ((listof any/c) (listof any/c) . -> . (listof any/c))]))

(module flatten racket
  (provide/contract [flatten (any/c . -> . (listof any/c))])
  (require (submod ".." lib))
  (define (flatten x)
    (cond
      [(empty? x) empty]
      [(cons? x) (append [flatten (car x)] [flatten (cdr x)])]
      [else (cons x empty)])))

(require 'flatten)
(flatten •)
