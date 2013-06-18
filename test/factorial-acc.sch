(module fac
  (provide
   [fac (int? . -> . int?)])
  (define (fac n)
    (fac-acc n 1))
  (define (fac-acc n acc)
    (if (zero? n) acc
        (fac-acc (sub1 n) (* n acc)))))

(require fac)
(fac •)