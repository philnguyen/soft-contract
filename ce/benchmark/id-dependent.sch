(module opaque
  (provide [n number?]))

(module id
  (provide
   [f (->i ([x number?]) (res (x) (=/c x)))])
  (define (f x) x))

(require opaque id)
(f n)
