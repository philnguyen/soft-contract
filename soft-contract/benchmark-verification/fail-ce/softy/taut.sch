(module taut racket
  (provide/contract
   [taut ([μ/c (X) (or/c boolean? number? [boolean? . -> . X])] . -> . boolean?)])
  (define (taut b)
    (cond
      [(procedure? b) (and (taut (b #t)) (taut (b #f)))]
      [else b])))

(require 'taut)
(taut •)
