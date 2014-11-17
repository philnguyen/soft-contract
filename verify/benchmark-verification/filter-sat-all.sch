(module filter-dep
  (provide
   [filter ([p? : (any . -> . any)] [xs : (listof any)] . -> . (listof (λ (x) (p? x))))])
  (define (filter p? xs)
    (cond
      [(empty? xs) empty]
      [else (let ([x (car xs)]
                  [zs (filter p? (cdr xs))])
              (if (p? x) (cons x zs) zs))])))

(require filter-dep)
(filter • •)