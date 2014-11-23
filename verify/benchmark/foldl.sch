(module foldl
  (provide
   [foldl ((any any . -> . any) any (listof any) . -> . any)])
  (define (foldl f z xs)
    (if (empty? xs) z
        (foldl f (f (car xs) z) (cdr xs)))))

(require foldl)
(foldl • • •)