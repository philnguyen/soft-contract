(module fold_left racket
  (provide/contract
   [main (integer? integer? . -> . (not/c false?))])
  
  (define (fold_left f acc xs)
    (cond [(empty? xs) acc]
          [else (fold_left f (f acc (car xs)) (cdr xs))]))

  (define (make_list n)
    (if (< n 0) empty (cons n (make_list (- n 1)))))

  (define (add x y) (+ x y))

  (define (main n m)
    (let ([xs (make_list n)])
      (> #|HERE|# (fold_left add m xs) m))))

(require 'fold_left)
(main • •)
