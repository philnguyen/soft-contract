(module foldr
  (provide
   [foldr ((num? bool? . -> . bool?) bool? (listof any) . -> . bool?)])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f #|HERE|# (foldr f z (cdr xs)) (car xs)))))

(require foldr)
(foldr • • •)
