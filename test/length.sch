(module len
  (provide
   [len ([l : (listof any)] . -> . (and/c
                                    (and/c int? (or/c zero? positive?))
                                    (λ (n) (equal? (empty? l) (zero? n)))))])
  (define (len xs)
    (if (empty? xs) 0
        (+ 1 (len (cdr xs))))))

(require len)
(len •)