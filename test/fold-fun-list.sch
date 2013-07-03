(module fold-fun-list
  (provide
   [mk-list (int? . -> . (listof (int? . -> . int?)))]
   [foldr (((int? . -> . int?) (int? . -> . int?) . -> . (int? . -> . int?))
           (int? . -> . int?)
           (listof (int? . -> . int?))
           . -> . (int? . -> . int?))]
   [main ([n : int?] . -> . (and/c (int? . -> . int?)
                                   (λ (f) (not (negative? (f 0))))))])
  (define (mk-list n)
    (if (positive? n) (cons (λ (m) (+ m n)) (mk-list (- n 1))) empty))
  (define (foldr f z xs)
    (if (empty? xs) z (f (car xs) (foldr f z (cdr xs)))))
  (define (compose f g) (λ (x) (f (g x))))
  (define (main n)
    (let [xs (mk-list n)]
      (foldr compose (λ (x) x) xs))))

(require fold-fun-list)
(main •)