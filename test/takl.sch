(module takl
  (provide
   [mas ((listof int?) (listof int?) (listof int?) . -> . (listof int?))]
   [listn (int? . -> . (listof int?))]
   [shorter? ((listof int?) (listof int?) . -> . any)])
  
  (define (listn n)
    (if (zero? n) empty (cons n (listn (- n 1)))))
  
  (define (shorter? x y)
    (and (not (empty? y))
         (or (empty? x) (shorter? (cdr x) (cdr y)))))
  
  (define (mas x y z)
    (if (not (shorter? y x)) z
        (mas (mas (cdr x) y z)
             (mas (cdr y) z x)
             (mas (cdr z) x y)))))

(require takl)
(mas • • •)