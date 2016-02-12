(module map_filter racket
  (provide/contract
   [main (integer? . -> . any/c)])
  
  (define (make_list m)
    (if (<= m 0) empty (cons 0 (make_list (- m 1)))))

  (define (make_list_list m)
    (if (<= m 0) empty (cons (make_list 0) (make_list_list (- m 1)))))

  (define (ne xs)
    (if (empty? xs) #|HERE|# 1 0))

  (define (filter p xs)
    (cond [(empty? xs) empty]
          [else (if (= 1 (p (car xs)))
                    (cons (car xs) (filter p (cdr xs)))
                    (filter p (cdr xs)))]))

  (define (map f xs)
    (cond [(empty? xs) empty]
          [else (cons (f (car xs)) (map f (cdr xs)))]))

  (define (main m)
    (map car (filter ne (make_list_list m)))))

(require 'map_filter)
(main •)
