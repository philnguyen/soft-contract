(module foldr
  (provide
   [foldr ((number? bool? . -> . bool?) bool? (listof any/c) . -> . bool?)])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f #|HERE|# (foldr f z (cdr xs)) (car xs)))))

(require foldr)
(foldr • • •)
