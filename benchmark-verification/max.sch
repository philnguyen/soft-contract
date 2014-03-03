(module max
  (provide [max ((int? int? . -> . int?) int? int? int? . -> . int?)])
  (define (max max2 x y z) (max2 (max2 x y) z)))

(module f (provide [f (int? int? . -> . int?)])
  (define (f x y) (if (>= x y) x y)))

(module main
  (provide [main ([x : int?] [y : int?] [z : int?]
                             . -> . (and/c int? (λ (m) (= (f x m) m))))])
  (require max f)
  (define (main x y z)
    (max f x y z)))

(require main)
(main • • •)