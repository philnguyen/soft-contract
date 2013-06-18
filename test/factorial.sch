(module fac
  (provide
   [fac (int? . -> . int?)])
  (define (fac n)
    (if (zero? n) 1 (* n (fac (sub1 n))))))

(require fac)
(fac •)