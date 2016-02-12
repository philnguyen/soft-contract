(module length racket
  (provide/contract
   [main (integer? . -> . (not/c false?))])
  
  (define (length xs)
    (cond [(empty? xs) 0]
          [else (+ 1 (length (cdr xs)))]))

  (define (make_list n)
    (if (= n 0) empty (cons n (make_list (- n 1)))))

  (define (main n)
    (let ([xs (make_list n)])
      (= n (length xs)))))

(require 'length)
(main •)
