(module f racket
  (provide/contract [f (integer? (integer? . -> . any/c) . -> . any/c)])
  (define (f x g) (g x)))
(module h racket
  (provide/contract [h (->i ([z integer?]) (res (z) ((and/c integer? (>/c z)) . -> . any/c)))])
  (define (h z) (λ (y) 'unit)))
(module main racket
  (provide/contract [main (integer? . -> . any/c)])
  (require (submod ".." f) (submod ".." h))
  (define (main n)
    (if (> n 0) (f n (h n)) 'unit)))

(require 'main)
(main •)
