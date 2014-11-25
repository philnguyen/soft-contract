(module foldr
  (provide
   [foldr ((any/c any/c . -> . any/c) any/c (listof any/c) . -> . any/c)])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f (car xs) (foldr f z (cdr xs))))))

(require foldr)
(foldr • • •)
