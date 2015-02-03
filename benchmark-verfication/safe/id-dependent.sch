(module opaque racket
  (provide/contract [n real?]))

(module id racket
  (provide/contract [f (->i ([x real?]) (res (x) (=/c x)))])
  (define (f x) x))

(require 'opaque 'id)
(f n)
