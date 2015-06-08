(module tak racket
  (provide/contract
   [tak (number? number? number? (number? . -> . number?) . -> . number?)])
  (define (tak x y z k)
    (if (not (< y x))
        (k z)
        (tak (- x 1)
             y
             z
             (lambda (v1)
               (tak (- y 1)
                    z
                    x
                    (lambda (v2)
                      (tak (- z 1)
                           x
                           y
                           (lambda (v3)
                             (tak v1 v2 v3 k))))))))))

(module nums racket
  (provide/contract [a number?] [b number?] [c number?]))

(require 'tak 'nums)
(tak a b c (lambda (x) x))
