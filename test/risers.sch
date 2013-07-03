(module risers
  (provide
   [risers ((listof int?) . -> . (listof (listof int?)))]
   [risers-else (int? (nelistof (listof int?))
                      . -> . (cons/c (cons/c int? empty?) (nelistof (listof int?))))]
   [risers-then (int? (nelistof (listof int?))
                      . -> . (cons/c (nelistof int?) (listof (listof int?))))])
  (define (risers l)
    (cond
      [(empty? l) empty]
      [(empty? (cdr l)) (cons (cons (car l) empty) empty)]
      [else (let ([x (car l)]
                  [y (car (cdr l))]
                  [etc (cdr (cdr l))])
              (if (< x y)
                  (risers-then x (risers (cons y etc)))
                  (risers-else x (risers (cons y etc)))))]))
  (define (risers-else x ss) (cons (cons x empty) ss))
  (define (risers-then x s:ss)
    (let ([s (car s:ss)]
          [ss (cdr s:ss)])
      (cons (cons x s) ss))))

(require risers)
(risers •)