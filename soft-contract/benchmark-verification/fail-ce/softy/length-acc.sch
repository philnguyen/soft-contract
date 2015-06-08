(module len racket
  (provide/contract
   [len (->i ([l (listof any/c)]) (res (l) (and/c integer? (>/c 0))))])
  (define (len xs)
    (len-acc xs 0))
  (define (len-acc xs acc)
    (if (empty? xs) acc
        (len-acc (cdr xs) (+ 1 acc)))))

(require 'len)
(len •)
