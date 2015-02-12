(module lib racket
  (provide (contract-out [even? (integer? . -> . boolean?)]
			 [odd? (integer? . -> . boolean?)])))
(module gcd2 racket
   (provide (contract-out (gcd2 (integer? integer? . -> . integer?))))
   (require (submod ".." lib))
   (define (gcd2 a b)
     (cond
      [(= a 0) b]
      [(= b 0) a]
      [(and (even? a) (even? b)) (* 2 (gcd2 (/ a 2) (/ b 2)))]
      [(and (even? a) (odd? b)) (gcd2 (/ a 2) b)]
      [(and (odd? a) (even? b)) (gcd2 a (/ b 2))]
      [(and (odd? a) (odd? b) (>= a b)) (gcd2 (/ (- a b) 2) b)]
      [else (gcd2 (/ (- b a) 2) a)])))

(require 'gcd2)

(equal? (gcd2 0 1337) 1337)
(equal? (gcd2 1337 0) 1337)
(equal? (gcd2 2 4) (* 2 (gcd2 1 2)))
(equal? (gcd2 2 5) (gcd2 1 5))
(equal? (gcd2 5 10) (gcd2 5 5))
(equal? (gcd2 9 7) (gcd2 (/ (- 9 7) 2) 7))
(equal? (gcd2 7 9) (gcd2 (/ (- 9 7) 2) 7))
(equal? (gcd2 10 17) 1)
(equal? (gcd2 17 10) 1)
(equal? (gcd2 60 10) 10)
(equal? (gcd2 30 45) 15)
