(module foldl racket
  (provide/contract
   [foldl ((number? boolean? . -> . boolean?) boolean? (listof number?) . -> . boolean?)])
  (define (foldl f z xs)
    (if (empty? xs) z
        (foldl f (f #|HERE|# z (car xs)) (cdr xs)))))

(require 'foldl)
(foldl • • •)
