(module ex-13 racket
  (provide/contract [f (any/c any/c . -> . (not/c false?))])
  (define (f x y)
    (cond
      [(and (number? x) (string? y)) (and (number? x) (string? y))]
      [(number? x) (and (number? x) (not (string? y)))]
      [else #|HERE|# (number? x)])))
(require 'ex-13)
(f • •)
