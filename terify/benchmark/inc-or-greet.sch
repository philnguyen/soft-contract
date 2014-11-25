(module lib
  (provide [string-append (string? string? . -> . string?)]))

(module inc-or-greet
  (provide [inc-or-greet (bool? (or/c string? integer?) . -> . (or/c #|HERE|# #;false? integer? string?))])
  (require lib)
  (define (inc-or-greet mode y)
    (if mode
        (if (integer? y) (+ y 1) #f)
        (if (string? y) (string-append "Hello" y) #f))))

(require inc-or-greet)
(inc-or-greet • •)
