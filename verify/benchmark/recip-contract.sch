(module recip
  (provide [recip (non-zero/c . -> . non-zero/c)]
           [non-zero/c any/c])
  (define (recip x) (/ 1 x))
  (define non-zero/c (and/c number? (not/c zero?))))

(require recip)
(recip •)
