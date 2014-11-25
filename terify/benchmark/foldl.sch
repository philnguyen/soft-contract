(module foldl
  (provide
   [foldl ((number? bool? . -> . bool?) bool? (listof number?) . -> . bool?)])
  (define (foldl f z xs)
    (if (empty? xs) z
        (foldl f (f #|HERE|# z (car xs)) (cdr xs)))))

(require foldl)
(foldl • • •)
