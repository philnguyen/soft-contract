(module list
  (provide
   [reverse ((listof int?) . -> . (listof int?))]
   [mk-list (int? . -> . (listof int?))]
   [append ((listof int?) (listof int?) . -> . (listof int?))])
  (define (reverse xs)
    (if (empty? xs) empty
        (append (reverse (cdr xs)) (cons (car xs) empty))))
  (define (mk-list n)
    (if (zero? n) empty
        (cons n (mk-list (- n 1)))))
  (define (append l r)
    (if (empty? l) r
        (cons (car l) (append (cdr l) r)))))

(module main
  (provide [main (int? . -> . int?)])
  (require list)
  (define (main len)
    (let [xs (mk-list len)]
      (if (positive? len)
          (car (reverse xs))
          0))))

(require main)
(main •)