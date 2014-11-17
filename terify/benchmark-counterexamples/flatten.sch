(module lib
  (provide [append ((listof any) (listof any) . -> . (listof any))]))

(module flatten
  (provide [flatten (any . -> . (listof any))])
  (require lib)
  (define (flatten x)
    (cond
      [(empty? x) empty]
      [(cons? x) (append [flatten (car x)] (cdr x) #|HERE|##;[flatten ])]
      [else (cons x empty)])))

(require flatten)
(flatten •)
