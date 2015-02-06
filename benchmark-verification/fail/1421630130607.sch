(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))

  (define (split-snd raw)
    (define splt (string-split raw))
    (cond [(empty? splt)             #f]
          [(empty? (cdr splt))       #f]
          [(empty? (cdr (cdr splt))) (car (cdr splt))]
          [else                      (displayln "Ignoring extra arguments")
                                     (car (cdr splt))]))

  
)
