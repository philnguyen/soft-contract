(abbrev/c non-zero? (and/c num? (not/c zero?)))

(module recip
  (provide [recip (non-zero? . -> . non-zero?)])
  (define (recip x) (/ 1 x)))

(require recip)
(recip •)