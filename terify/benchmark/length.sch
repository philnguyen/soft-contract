(module len
  (provide
   [len ([l : (listof any)] . -> . (and/c int? (>=/c 0)))])

  (define (len xs)
    (if (empty? xs) 0
        (+ 1 (len (cdr xs))))))

(require len)
(len •)