(module lib racket
  (provide
   (contract-out
    ;; `substring`'s contract is not precise enough. It's not `f`'s fault.
    (substring (string? (and/c integer? (>=/c 0)) (and/c integer? (>=/c 0)) . -> . string?)))))

(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))
  (require (submod ".." lib))

  (define (split-snd x)
    (substring x 2 3)))
