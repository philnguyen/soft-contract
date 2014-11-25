(module keygen
  (require prime?)
  (provide [keygen (any/c . -> . (λ (x) (prime? x)))]))

(module rsa
  (require prime?)
  (provide [rsa ((λ (x) (prime? x)) any/c . -> . any/c)]))

(module prime?
  (provide [prime? (any/c . -> . any/c)]))

(module enc
  (provide [enc (any/c . -> . any/c)])
  (require rsa keygen)
  (define (enc x) (rsa (keygen #t) x)))

(require enc)
(enc •)
