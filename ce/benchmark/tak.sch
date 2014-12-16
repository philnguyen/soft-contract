(module tak
  (provide
   [tak (integer? integer? integer? . -> . integer?)])
  (define (tak x y z)
    (if (false? (< y x)) z
        (tak (tak (- x 1) y z)
             (tak (- y 1) z x)
             (tak (- z 1) x y)))))
(module nums
  (provide [a integer?] [b integer?] [c integer?]))

(require tak nums)
(tak a b c)
