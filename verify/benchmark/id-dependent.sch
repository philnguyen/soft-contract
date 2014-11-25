(module opaque
  (provide [n number?]))

(module id
  (provide
   [f ([x : number?] . -> . (=/c x))])
  (define (f x) x))

(require opaque id)
(f n)
