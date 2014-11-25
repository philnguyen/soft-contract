(module foldl1
  (provide [foldl1 ((any/c any/c . -> . any/c) (nelistof any/c) . -> . any/c)])
  (define (foldl1 f xs)
    (let ([z (car xs)]
          [zs (cdr xs)])
      (if (empty? zs) z
          (foldl1 f (cons (f z (car zs)) (cdr zs)))))))

(require foldl1)
(foldl1 • •)
