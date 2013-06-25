(abbrev/c non-zero? (and/c num? (λ (x) (not (zero? x)))))

(module recip
  (provide [recip (non-zero? . -> . non-zero?)])
  (define (recip x) (/ 1 x)))

(require recip)
(recip •)