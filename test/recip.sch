(module recip
  (provide [recip (any . -> . (or/c (and/c num? (λ (x) (not (zero? x)))) str?))])
  (define (recip x)
    (if (and (num? x) (not (zero? x)))
        (/ 1 x)
        "expect non-zero number")))

(require recip)
(recip •)