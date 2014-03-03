(module foldr
  (provide
   [foldr ((any any . -> . any) any (listof any) . -> . any)])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f (car xs) (foldr f z (cdr xs))))))

(require foldr)
(foldr • • •)