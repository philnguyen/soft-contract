(module recip
  (provide [recip (any . -> . (or/c (and/c num? (not/c zero?)) str?))])
  (define (recip x)
    (if (and (num? x) (not (zero? x)))
        (/ 1 x)
        "expect non-zero number")))

(require recip)
(recip •)