(module opaque racket
  (provide/contract [n number?]))

(module id racket
  (provide/contract [f (->i ([x number?]) (res (x) (=/c x)))])
  (define (f x) x))

(require 'opaque 'id)
(f n)
