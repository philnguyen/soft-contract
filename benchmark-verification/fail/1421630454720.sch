(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))
  
  (define (substring x)
    (list->string (string->list x)))

  (define (split-snd x)
    (substring x 2 3))
  
)
