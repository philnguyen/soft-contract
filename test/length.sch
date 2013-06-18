(module len
  (provide
   [len ((listof any) . -> . int?)])
  (define (len xs)
    (if (empty? xs) 0
        (add1 (len (cdr xs))))))

(require len)
(len •)