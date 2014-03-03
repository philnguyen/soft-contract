(module Y
  (provide [Y (([any . -> . any] . -> . [any . -> . any]) . -> . [any . -> . any])])
  (define (Y f)
    (λ (y)
      (((λ (x) (f (λ (z) ((x x) z))))
        (λ (x) (f (λ (z) ((x x) z)))))
       y))))

(module last
  (require Y)
  (provide [last ((cons/c any (listof any)) . -> . any)])
  (define (last l)
    ((Y (λ (f)
          (λ (x)
            (if (empty? (cdr x)) (car x) (f (cdr x))))))
     l)))

(require last)
(last •)