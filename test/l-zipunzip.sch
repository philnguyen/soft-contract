(module l-zipunzip
  (provide
   [f ((int? int? . -> . int?) . -> . (int? int? . -> . int?))]
   [unzip (int? (int? int? . -> . int?) . -> . int?)]
   [zip (int? int? . -> . int?)]
   [main (int? . -> . int?)])
  
  (define (f g) (λ (x y) (g (+ x 1) (+ y 1))))
  (define (unzip x k)
    (if (zero? x) (k 0 0)
        (unzip (- x 1) (f k))))
  (define (zip x y)
    (if (zero? x)
        (if (zero? y) 0 (/ 1 0 #|FAIL|#))
        (if (zero? y) (/ 1 0 #|FAIL|#)
            (+ 1 (zip (- x 1) (- y 1))))))
  (define (main n)
    (unzip n zip)))

(require l-zipunzip)
(main •)