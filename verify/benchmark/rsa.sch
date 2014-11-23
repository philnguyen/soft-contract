(module keygen
  (require prime?)
  (provide [keygen (any . -> . (λ (x) (prime? x)))]))

(module rsa
  (require prime?)
  (provide [rsa ((λ (x) (prime? x)) any . -> . any)]))

(module prime?
  (provide [prime? (any . -> . any)]))

(module enc
  (provide [enc (any . -> . any)])
  (require rsa keygen)
  (define (enc x) (rsa (keygen #t) x)))

(require enc)
(enc •)