(module forall_leq racket
  (provide/contract
   [main (integer? . -> . (not/c false?))])
  
  (define (for_all f xs)
    (cond [(empty? xs) #t]
          [else (and (f (car xs)) (for_all f (cdr xs)))]))

  (define (check x) (>= x 0))
  
  (define (make_list n)
    (if (< n 0) empty (cons n (make_list (- n 1)))))

  (define (main n)
    (for_all check (make_list n))))

(require 'forall_leq)
(main •)
