(module list
  (provide [reverse ((listof int?) (listof int?) . -> . (listof int?))]
           [mk-list (int? . -> . (listof int?))])
  (define (reverse l ac)
    (if (empty? l) ac (reverse (cdr l) (cons (car l) ac))))
  (define (mk-list n)
    (if (= n 0) empty (cons n (mk-list (- n 1))))))

(module main
  (provide [main (int? . -> . int?)])
  (require list)
  (define (main len)
    (let [xs (mk-list len)]
      (if (> len 0) (car (reverse xs empty)) 0))))

(require main)
(main •)