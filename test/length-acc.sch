(module len
  (provide
   [len ((listof any) . -> . int?)])
  (define (len xs)
    (len-acc xs 0))
  (define (len-acc xs acc)
    (if (empty? xs) acc
        (len-acc (cdr xs) (add1 acc)))))

(require len)
(len •)