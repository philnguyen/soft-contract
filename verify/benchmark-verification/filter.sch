(module filter
  (provide
   [filter ((any . -> . any) (listof any) . -> . (listof any))])
  (define (filter p? xs)
    (cond
      [(empty? xs) empty]
      [else (let ([x (car xs)]
                  [zs (filter p? (cdr xs))])
              (if (p? x) (cons x zs) zs))])))

(require filter)
(filter • •)