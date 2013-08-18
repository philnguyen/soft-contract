(module f
  (provide [f ([x : (any . -> . int?)]
               . -> .
               ((and/c (any . -> . int?)
                       (λ (y) (not (and (> (x #f) 0) (< (y #f) 0))))) . -> . int?))]))

(module h (provide [h (int? . -> . (any . -> . int?))])
  (define (h x) (λ (_) x)))

(module g (provide [g (int? . -> . int?)])
  (require f h)
  (define (g n) ((f (h n)) (h n))))

(module main (provide [main (int? . -> . int?)])
  (require g)
  (define (main m) (g m)))

(require main)
(main •)