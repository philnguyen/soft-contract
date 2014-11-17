(module rand (provide (rand (-> int?))))

(module fold-div
  (provide
   [foldl ((real? real? . -> . real?) real? (listof real?) . -> . real?)]
   [randpos (-> int?)]
   [mk-list (int? . -> . (listof (and/c int? positive?)))]
   [main (int? int? . -> . real?)])
  (require rand)
  (define (foldl f z l)
    (if (empty? l) z (foldl f (f z (car l)) (cdr l))))
  (define (randpos)
    (let [n (rand)] (if (> n 0) n (randpos))))
  (define (mk-list n)
    (if (#|HERE|##;<= < n 0) empty
        (cons (randpos) (mk-list (- n 1)))))
  (define (main n m) (foldl / m (mk-list n))))

(require fold-div)
(main • •)
