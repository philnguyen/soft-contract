(module len
  (provide
   [len ([l : (listof any)] . -> . (and/c int? (>=/c 0)))])
  (define (len xs)
    (len-acc xs 0))
  (define (len-acc xs acc)
    (if (empty? xs) acc
        (len-acc (cdr xs) (+ 1 acc)))))

(require len)
(len •)