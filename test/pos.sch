(module pos
  (provide
   [pos/c any]
   [mk-pos (real? real? . -> . pos/c)])
  (define pos/c ([msg : (one-of/c 'x 'y)] . -> . real?)))

(module posd
  (provide
   [posd/c any]
   [mk-posd (pos/c . -> . posd/c)])
  (require pos)
  (define posd/c
    ([msg : (one-of/c 'x 'y 'dist0)]
     . -> .
     (cond
       [(equal? msg 'dist0) (and/c real? (>=/c 0))]
       [else real?])))
  (define (mk-posd pos)
    (λ (m)
      (cond
        [(equal? m 'dist0) (let ([x (pos 'x)]
                                 [y (pos 'y)])
                             (sqrt (+ (* x x) (* y y))))]
        [else (pos m)]))))

(require posd)
(• mk-posd)