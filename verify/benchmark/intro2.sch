(module f racket
  (provide/contract [f (integer? (integer? . -> . any/c) . -> . any/c)])
  (define (f x g) (g (+ x 1))))
(module h racket
  (provide/contract [h ((and/c integer? (>/c 0)) . -> . any/c)])
  (define (h y) 'unit))
(module main racket
  (provide/contract [main (integer? . -> . any/c)])
  (require (submod ".." f) (submod ".." h))
  (define (main n)
    (if (>= n 0) (f n h) 'unit)))

(require 'main)
(main •)
