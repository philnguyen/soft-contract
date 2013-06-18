(module strnum?
  (provide [strnum? (any . -> . bool?)])
  (define (strnum? x)
    (or (str? x) (num? x))))
(module opaque (provide [opaque any]))

(require strnum? opaque)
(let ([v opaque])
  (if (strnum? v)
      (cond
        [(num? v) "good"]
        [(str? v) "good"]
        [else "bad"])
      "good"))