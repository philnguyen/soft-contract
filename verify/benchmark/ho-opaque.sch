(module db1 racket
  (provide/contract
   [db1 ([zero? . -> . zero?] . -> . [zero? . -> . zero?])])
  (define (db1 f)
    (λ (x) (f (f x)))))

(module f racket
  (provide/contract 
   [f (zero? . -> . number?)]))

(require 'db1 'f)
((db1 f) 0)
