(module foldl
  (provide
   [foldl ((num? bool? . -> . bool?) bool? (listof num?) . -> . bool?)])
  (define (foldl f z xs)
    (if (empty? xs) z
        (foldl f (f #|HERE|# z (car xs)) (cdr xs)))))

(require foldl)
(foldl • • •)
