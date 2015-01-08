(module Y racket
  (provide/contract
   [Y (([any/c . -> . any/c] . -> . [any/c . -> . any/c]) . -> . [any/c . -> . any/c])])
  (define (Y f)
    (λ (y)
      (((λ (x) (f (λ (z) ((x x) z))))
        (λ (x) (f (λ (z) ((x x) z)))))
       y))))

(module last racket
  (require (submod ".." Y))
  (provide/contract [last (#|HERE|#(listof any/c) . -> . any/c)])
  (define (last l)
    ((Y (λ (f)
          (λ (x)
            (if (empty? (cdr x)) (car x) (f (cdr x))))))
     l)))
