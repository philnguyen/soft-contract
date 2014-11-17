(module recip
  (provide [recip (non-zero/c . -> . non-zero/c)]
           [non-zero/c any])
  (define (recip x) (/ 1 x))
  (define non-zero/c (and/c num? (not/c zero?))))

(require recip)
(recip •)