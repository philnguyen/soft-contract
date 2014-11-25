(module rand (provide (rand (-> integer?))))

(module fold-div
  (provide
   [foldl ((real? real? . -> . real?) real? (listof real?) . -> . real?)]
   [randpos (-> integer?)]
   [mk-list (integer? . -> . (listof (and/c integer? positive?)))]
   [main (integer? integer? . -> . real?)])
  (require rand)
  (define (foldl f z l)
    (if (empty? l) z (foldl f (f z (car l)) (cdr l))))
  (define (randpos)
    (let [n (rand)] (if (> n 0) n (randpos))))
  (define (mk-list n)
    (if (<= n 0) empty
        (cons (randpos) (mk-list (- n 1)))))
  (define (main n m) (foldl / m (mk-list n))))

(require fold-div)
(main • •)
