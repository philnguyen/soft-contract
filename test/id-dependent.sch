(module opaque
  (provide [n num?]))

(module id
  (provide
   [f ([x : num?] . -> . (λ (y) (= x y)))])
  (define (f x) x))

(require opaque id)
(f n)