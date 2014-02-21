(module lib
  (provide [string-append (str? str? . -> . str?)]))

(module inc-or-greet
  (provide [inc-or-greet (bool? (or/c str? int?) . -> . (or/c false? int? str?))])
  (require lib)
  (define (inc-or-greet mode y)
    (if mode
        (if (int? y) (+ y 1) #f)
        (if (str? y) (string-append "Hello" y) #f))))

(require inc-or-greet)
(inc-or-greet • •)