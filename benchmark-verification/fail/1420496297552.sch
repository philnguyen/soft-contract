(module foldl1 racket
  (provide/contract [foldl1 ((any/c any/c . -> . any/c) (#|HERE|# listof any/c) . -> . any/c)])
  (define (foldl1 f xs)
    (let ([z (car xs)]
          [zs (cdr xs)])
      (if (empty? zs) z
          (foldl1 f (cons (f z (car zs)) (cdr zs)))))))
 (module user racket
  (require (submod ".." foldl1))
  (foldl1 (λ (x y) 0.840) empty))
