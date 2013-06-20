(module keygen
  (require prime?)
  (provide [keygen (any . -> . prime?)]))

(module rsa
  (require prime?)
  (provide [rsa (prime? any . -> . any)]))

(module prime?
  (provide [prime? (any . -> . any)]))

(module enc
  (provide [enc (any . -> . any)])
  (require rsa keygen)
  (define (enc x) (rsa (keygen #t) x)))

(require enc)
(enc •)