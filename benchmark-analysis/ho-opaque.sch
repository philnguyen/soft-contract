(module db1
  (provide
   [db1 ([zero? . -> . zero?] . -> . [zero? . -> . zero?])])
  (define (db1 f)
    (λ (x) (f (f x)))))

(module f
  (provide 
   [f (zero? . -> . num?)]))

(require db1 f)
((db1 f) 0)