(module foldl
  (provide
   [foldl ((any/c any/c . -> . any/c) any/c (listof any/c) . -> . any/c)])
  (define (foldl f z xs)
    (if (empty? xs) z
        (foldl f (f (car xs) z) (cdr xs)))))

(require foldl)
(foldl • • •)
