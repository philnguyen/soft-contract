(module flatten
  (provide
   [append ((listof any) (listof any) . -> . (listof any))]
   [flatten (any . -> . (listof any))])
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys))))
  (define (flatten x)
    (cond
      [(empty? x) empty]
      [(cons? x) (append [flatten (car x)] [flatten (cdr x)])]
      [else (cons x empty)])))

(require flatten)
(flatten •)