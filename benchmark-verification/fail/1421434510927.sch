(module foo racket
 
  (define (div2 n)
    (/ n 2)))

(require 'foo)
(div2 5)

