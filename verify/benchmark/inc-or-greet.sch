(module lib racket
  (provide/contract [string-append (string? string? . -> . string?)]))

(module inc-or-greet racket
  (provide/contract [inc-or-greet (boolean? (or/c string? integer?) . -> . (or/c false? integer? string?))])
  (require (submod ".." lib))
  (define (inc-or-greet mode y)
    (if mode
        (if (integer? y) (+ y 1) #f)
        (if (string? y) (string-append "Hello" y) #f))))

(require 'inc-or-greet)
(inc-or-greet • •)
