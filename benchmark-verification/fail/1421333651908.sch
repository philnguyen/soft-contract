(module foldl1 racket
  (provide
    (contract-out
      [foldl1 ((any/c any/c . -> . any/c) (listof any/c) . -> . any/c)]))
  (define (foldl1 f xs)
    (let ([z (car xs)]
          [zs (cdr xs)])
      (if (empty? zs) z
          (foldl1 f (cons (f z (car zs)) (cdr zs)))))))
