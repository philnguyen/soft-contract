(module carnum?
  (provide [carnum? (cons? . -> . bool?)])
  (define (carnum? p) (num? (car p))))

(module opaque
  (provide [opaque cons?]))

(require opaque carnum?)
(let ([p opaque])
  (if (carnum? p)
      (if (num? (car p)) "good" "bad")
      (if (false? (num? (car p))) "good" "bad")))