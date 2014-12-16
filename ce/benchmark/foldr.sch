(module foldr
  (provide
   [foldr ((number? boolean? . -> . boolean?) boolean? (listof any/c) . -> . boolean?)])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f #|HERE|# (foldr f z (cdr xs)) (car xs)))))

(require foldr)
(foldr • • •)
