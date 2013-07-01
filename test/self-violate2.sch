(module f ; naive approximation can cause false blame and miss real result
  (provide [f (int? . -> . int?)])
  (define (f x)
    (cond
      [(int? x) (str-len (f "anything"))]
      [else "secret"])))

(require f)
(f •)