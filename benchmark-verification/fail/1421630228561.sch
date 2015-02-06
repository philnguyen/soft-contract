(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))

  (define (split-snd raw)
    (cond [(empty? (string-split raw))             #f]
          [(empty? (cdr (string-split raw)))       #f]
          [(empty? (cdr (cdr (string-split raw)))) (car (cdr (string-split raw)))]
          [else                      (displayln "Ignoring extra arguments")
                                     (car (cdr (string-split raw)))]))

  
)
