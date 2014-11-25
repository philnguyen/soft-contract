(module carnum?
  (provide [carnum? (->i ([p cons?]) (res (p) (and/c bool? (λ (a) (equal? a (number? (car p)))))))])
  (define (carnum? p) (number? (car p))))

(require carnum?)
(carnum? •)
