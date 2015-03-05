(module recip racket
  (provide/contract [recip (any/c . -> . (or/c (and/c number? (not/c zero?)) string?))])
  (define (recip x)
    (if (and (number? x) (not (zero? x)))
        (/ 1 x)
        "expect non-zero number")))

(require 'recip)
(recip •)
