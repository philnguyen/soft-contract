(module carnum?
  (provide [carnum? ([p : cons?] . -> . (and/c bool? (λ (a) (equal? a (num? (car p))))))])
  (define (carnum? p) (num? (car p))))

(require carnum?)
(carnum? •)