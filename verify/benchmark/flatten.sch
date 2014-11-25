(module lib
  (provide [append ((listof any/c) (listof any/c) . -> . (listof any/c))]))

(module flatten
  (provide [flatten (any/c . -> . (listof any/c))])
  (require lib)
  (define (flatten x)
    (cond
      [(empty? x) empty]
      [(cons? x) (append [flatten (car x)] [flatten (cdr x)])]
      [else (cons x empty)])))

(require flatten)
(flatten •)
