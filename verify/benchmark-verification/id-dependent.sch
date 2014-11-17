(module opaque
  (provide [n num?]))

(module id
  (provide
   [f ([x : num?] . -> . (=/c x))])
  (define (f x) x))

(require opaque id)
(f n)