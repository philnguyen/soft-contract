(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))
  
  (define (substring x)
    "foobar")

  (define (split-snd x)
    (substring x 2 3))
  
)
