(module db1
  (provide
   [db1 ([zero? . -> . zero?] . -> . [#|HERE|#number? . -> . zero?])])
  (define (db1 f)
    (λ (x) (f (f x)))))

(module f
  (provide 
   [f (zero? . -> . number?)]))

(require db1 f)
(• db1)
