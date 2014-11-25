(module eo
  (provide
   [even? (integer? . -> . bool?)]
   [odd? (integer? . -> . bool?)])
  (define (even? n)
    (if (zero? n) #t (odd? (sub1 n))))
  (define (odd? n)
    (if (zero? n) #f (even? (sub1 n)))))

(require eo)
(even? •)
