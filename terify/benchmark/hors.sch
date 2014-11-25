(module c (provide [c (integer? . -> . any/c)])
  (define (c _) 'unit))

(module b (provide [b ((integer? . -> . any/c) integer? . -> . any/c)])
  (define (b x _) (x 1)))

(module a (provide [a ((integer? . -> . any/c) (integer? . -> . any/c) zero? . -> . any/c)])
  (define (a x y q) (begin (x 0) (y 0))))

(module f (provide [f (integer? (integer? . -> . any/c) integer? . -> . any/c)])
  (require a b)
  (define (f n x q)
    (if (<= n 0) (x q)
        (a x (λ (p) (f (- n 1) (λ (_) (b x _)) p)) q))))

(module s (provide [s (integer? integer? . -> . any/c)])
  (require c f)
  (define (s n q) (f n c q)))

(module main (provide [main (integer? . -> . any/c)])
  (require s)
  (define (main n) (s n 0)))

(require main)
(main •)
