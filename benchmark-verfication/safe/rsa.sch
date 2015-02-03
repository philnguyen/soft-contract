(module keygen racket
  (require (submod ".." prime?))
  (provide/contract [keygen (any/c . -> . (λ (x) (prime? x)))]))

(module rsa racket
  (require (submod ".." prime?))
  (provide/contract [rsa ((λ (x) (prime? x)) any/c . -> . any/c)]))

(module prime? racket
  (provide/contract [prime? (any/c . -> . any/c)]))

(module enc racket
  (provide/contract [enc (any/c . -> . any/c)])
  (require (submod ".." rsa) (submod ".." keygen))
  (define (enc x) (rsa (keygen #t) x)))

(require 'enc)
(enc •)
