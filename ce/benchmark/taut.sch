(module taut racket
  (provide/contract
   [taut ([μ/c (X) (or/c boolean? [boolean? . -> . X])] . -> . boolean?)])
  (define (taut b)
    (cond
      [(boolean? b) b]
      [else (and (taut (b #t)) (taut (b #f)))])))

(require 'taut)
(taut •)
