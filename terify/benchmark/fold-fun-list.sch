(module fold-fun-list
  (provide
   [mk-list (int? . -> . (listof (int? . -> . int?)))]
   [foldr (((int? . -> . int?) (int? . -> . int?) . -> . (int? . -> . int?))
           (int? . -> . int?)
           (listof (int? . -> . int?))
           . -> . (int? . -> . int?))]
   [main ([n : int?] . -> . (and/c (int? . -> . int?)
                                   (λ (f) (>= (f 0) 0))))])
  (define (mk-list n)
    (if (< n 0) empty
        (cons (λ (m) (+ m n)) (mk-list (- n 1)))))
  (define (foldr f z xs)
    (if (empty? xs) z (f (car xs) (foldr f z (cdr xs)))))
  (define (compose f g) (λ (x) (f (g x))))
  (define (main n)
    (let [xs (mk-list n)]
      (foldr compose (λ (x) x) xs))))

(require fold-fun-list)
(main •)
