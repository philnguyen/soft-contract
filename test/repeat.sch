(module repeat
  (provide [repeat ([f : (any . -> . any)] [n : int?] [s : any]
                                           . -> . (λ (a) (implies (zero? n) (equal? a s))))])
  (define (repeat f n s)
    (if (zero? n) s (f (repeat f (- n 1) s)))))

(require repeat)
(repeat • • •)