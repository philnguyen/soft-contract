(module vec
  (provide
   [vec/c any])
  (define vec/c ([msg : (one-of/c 'x 'y)] . -> . real?)))

(module rich-vec
  (provide
   [rich-vec/c any]
   [enrich ((real? real? . -> . vec/c) . -> . (real? real? . -> . rich-vec/c))])
  (require vec)
  (define rich-vec/c
    ([msg : (one-of/c 'x 'y 'len)]
     . -> .
     (cond
       [(equal? msg 'len) (and/c real? (>=/c 0))]
       [else real?])))
  (define (enrich mk-vec)
    (λ (x y)
      (let ([vec (mk-vec x y)])
        (λ (m)
          (cond
            [(equal? m 'len) (let ([x (vec 'x)]
                                   [y (vec 'y)])
                               (sqrt (+ (* x x) (* y y))))]
            [else (vec m)]))))))

(require rich-vec)
(• enrich)