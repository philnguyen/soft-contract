(module nth0
  (provide
   [nth (int? (listof int?) . -> . int?)]
   [mk-list (int? . -> . (listof int?))]
   [main (int? . -> . int?)])
  (define (nth n xs)
    (if (zero? n) (car xs) (nth (- n 1) (cdr xs))))
  (define (mk-list n)
    (if (or (zero? n) (positive? n))
        (cons n (mk-list (- n 1)))
        empty))
  (define (main n)
    (let [xs (mk-list n)]
      (if (empty? xs) 0 (nth 0 xs)))))

(require nth0)
(main •)