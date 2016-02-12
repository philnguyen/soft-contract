(module fold_right racket
  (provide/contract
   [main (integer? integer? . -> . (not/c false?))])
  
  (define (fold_right f xs acc)
    (cond [(empty? xs) acc]
          [else (f (car xs) (fold_right f (cdr xs) acc))]))

  (define (make_list n)
    (if (< n 0) empty (cons n (make_list (- n 1)))))
  
  (define (add x y) (+ x y))
  
  (define (main n m)
    (let ([xs (make_list n)])
      (>= (fold_right add xs m) m))))

(require 'fold_right)
(main • •)
