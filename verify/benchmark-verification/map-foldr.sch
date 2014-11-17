(module map-foldr
  (provide
   [foldr ((any any . -> . any) any (listof any) . -> . any)]
   [map ((any . -> . any) (listof any) . -> . (listof any))])
  (define (foldr f z xs)
    (if (empty? xs) z
        (f (car xs) (foldr f z (cdr xs)))))
  (define (map f xs)
    (foldr (λ (x ys) (cons (f x) ys)) empty xs)))

(require map-foldr)
(map • •)