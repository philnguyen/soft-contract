(module len
  (provide
   [len ((listof any/c) . -> . (and/c integer? (>=/c 0)))])

  (define (len xs)
    (if (empty? xs) 0
        (+ 1 (len (cdr xs))))))

(require len)
(len •)
