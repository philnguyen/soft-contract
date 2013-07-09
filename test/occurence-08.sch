(module strnum?
  (provide [strnum? ([x : any] . -> . (and/c bool? (λ (a) (equal? a (or (str? x) (num? x))))))])
  (define (strnum? x)
    (or (str? x) (num? x))))

(require strnum?)
(strnum? •)