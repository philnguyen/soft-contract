(module taut
  (provide
   [taut ([μ X (or/c (or/c true? false?) [bool? . -> . X])] . -> . bool?)])
  (define (taut b)
    (cond
      [(bool? b) b]
      [else (and (taut (b #t)) (taut (b #f)))])))

(require taut)
(taut •)