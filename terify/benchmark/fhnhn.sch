(module f
  (provide [f ([x : (any/c . -> . integer?)]
               . -> .
               ((and/c (any/c . -> . integer?)
                       (λ (y) (not (and (> (x #f) 0) (< (y #f) 0))))) . -> . integer?))]))

(module h (provide [h (integer? . -> . (any/c . -> . integer?))])
  (define (h x) (λ (_) x)))

(module g (provide [g (integer? . -> . integer?)])
  (require f h)
  (define (g n) ((f (h n)) (h n))))

(module main (provide [main (integer? . -> . integer?)])
  (require g)
  (define (main m) (g m)))

(require main)
(main •)
