 (module f racket
  (provide/contract [f (cons? . -> . symbol?)])
  (require (submod ".." g))
  (define (f p)
    (if (and (number? (car p)) (number? (cdr p))) (g p) 'no)))

(module g racket
  (provide/contract [g ((cons/c number? number?) . -> . symbol?)]))

(require 'f)
(f •)
