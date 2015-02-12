(module lib racket
  (provide
   (contract-out [string-split (string? . -> . (listof string?))])))

(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))
  (require (submod ".." lib))

  (define (split-snd raw)
    (let ([splt (string-split raw)])
      (cond [(empty? splt)             #f]
          [(empty? (cdr splt))       #f]
          [(empty? (cdr (cdr splt))) (car (cdr splt))]
          [else                      #;(displayln "Ignoring extra arguments")
                                     (car (cdr splt))]))))
