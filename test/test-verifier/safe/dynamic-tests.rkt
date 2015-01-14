(module f racket
  (provide/contract
   [f ((or/c number? string?) cons? . -> . number?)])
  (define (f input extra)
    (cond
      [(and (number? input) (number? (car extra)))
       (+ input (car extra))]
      [(number? (car extra))
       (+ (string-length input) (car extra))]
      [else 0])))
