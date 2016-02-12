(module risers racket
  (provide/contract
   [main (integer? . -> . any/c)])
  
  (define (make_list m)
    (if (<= m 0) empty (cons 0 (make_list (- m 1)))))

  (define (risersElse x xs)
    (let ([s (car xs)]
          [ss (cdr xs)])
      (cons (list x) (cons s ss))))

  (define (risersThen x xs)
    (let ([s (car xs)]
          [ss (cdr xs)])
      (cons (cons x s) ss)))

  (define (risers xs)
    (cond [(empty? xs) empty]
          ;[(empty? (cdr xs)) (list (list (car xs)))]
          [else
           (let ([x (car xs)]
                 [y (car (cdr xs))]
                 [etc (cdr (cdr xs))])
             (cond [(< x y) (risersThen x (risers (cdr xs)))]
                   [else    (risersElse x (risers (cdr xs)))]))]))

  (define (main m)
    (risers (make_list m))))

(require 'risers)
(main •)
