(module carnum?
  (provide [carnum? (->i ([p cons?]) (res (p) (and/c boolean? (λ (a) (equal? a (number? (car p)))))))])
  (define (carnum? p) (number? (car p))))

(require carnum?)
(carnum? •)
