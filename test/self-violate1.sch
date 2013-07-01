(module f ; naive approximation can miss blame
  (provide [f (num? . -> . bool?)])
  (define (f x)
    (if (num? x) (f "") "")))

(require f)
(f •)