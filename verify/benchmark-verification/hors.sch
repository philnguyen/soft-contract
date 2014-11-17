(module c (provide [c (int? . -> . any)])
  (define (c _) 'unit))

(module b (provide [b ((int? . -> . any) int? . -> . any)])
  (define (b x _) (x 1)))

(module a (provide [a ((int? . -> . any) (int? . -> . any) zero? . -> . any)])
  (define (a x y q) (begin (x 0) (y 0))))

(module f (provide [f (int? (int? . -> . any) int? . -> . any)])
  (require a b)
  (define (f n x q)
    (if (<= n 0) (x q)
        (a x (λ (p) (f (- n 1) (λ (_) (b x _)) p)) q))))

(module s (provide [s (int? int? . -> . any)])
  (require c f)
  (define (s n q) (f n c q)))

(module main (provide [main (int? . -> . any)])
  (require s)
  (define (main n) (s n 0)))

(require main)
(main •)