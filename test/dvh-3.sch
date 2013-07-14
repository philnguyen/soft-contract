(module dvh-3
  (provide
   [succ ([x : num?] . -> . (lambda (z) (= (+ 1 x) z)))])

  (define (succ x) (+ 1 x)))

(require dvh-3)
(succ •)