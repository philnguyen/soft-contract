(module keygen
  (require prime?)
  (provide [keygen (any . -> . prime?)]))

(module rsa
  (require prime?)
  (provide [rsa (prime? any . -> . any)]))

(module prime?
  (provide [prime? (any . -> . any)]))

(require keygen rsa)
(rsa (keygen #t) "Plaintext")