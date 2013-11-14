(module taut
  (provide
   [taut ([μ/c (X) (or/c bool? [bool? . -> . X])] . -> . bool?)])
  (define (taut b)
    (cond
      [(bool? b) b]
      [else (and (taut (b #t)) (taut (b #f)))])))

(require taut)
(amb (if (bool? (taut •)) "good" "bad")
     (if (taut #t) "good" "bad")
     (if (taut false?) "bad" "good")
     (if (taut (λ (x) (λ (y) (and x y)))) "bad" "good"))