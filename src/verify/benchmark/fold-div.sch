(module fold-div racket
  (provide/contract
   [main (integer? integer? . -> . real?)])
  (define (foldl f z l)
    (if (empty? l) z (foldl f (f z (car l)) (cdr l))))
  (define (mk-list n)
    (if (<= n 0) empty
        (cons 0 (mk-list (- n 1)))))
  (define (main n m) (foldl / m (mk-list n))))

(require 'fold-div)
(main • •)
