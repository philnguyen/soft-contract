(module tak racket
  (provide/contract
   [tak (number? number? number? . -> . number?)])
  (define (tak x y z)
    (if (false? (< y x)) z
        (tak (tak (- x 1) y z)
             (tak (- y 1) z x)
             (tak (- z 1) x y)))))
(module nums racket
  (provide/contract [a number?] [b number?] [c number?]))

(require 'tak 'nums)
(tak a b c)
