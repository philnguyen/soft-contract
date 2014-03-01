(module taut
  (provide
   [taut ([μ/c (X) (or/c bool? [bool? . -> . X])] . -> . bool?)])
  (define (taut b)
    (cond
      [(bool? b) b]
      [else (and (taut (b #t)) (taut (b #f)))])))

(require taut)
(taut •)