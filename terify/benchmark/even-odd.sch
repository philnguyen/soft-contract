(module eo
  (provide
   [even? (int? . -> . bool?)]
   [odd? (int? . -> . bool?)])
  (define (even? n)
    (if (zero? n) #t (odd? (sub1 n))))
  (define (odd? n)
    (if (zero? n) #f (even? (sub1 n)))))

(require eo)
(even? •)