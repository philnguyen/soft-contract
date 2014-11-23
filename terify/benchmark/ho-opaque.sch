(module db1
  (provide
   [db1 ([zero? . -> . zero?] . -> . [#|HERE|#num? . -> . zero?])])
  (define (db1 f)
    (λ (x) (f (f x)))))

(module f
  (provide 
   [f (zero? . -> . num?)]))

(require db1 f)
(• db1)
