(module zip_unzip racket
  (provide/contract
   [main (integer? . -> . any/c)])
  
  (define (zip xs ys)
    (cond [(empty? xs)
           (if (empty? ys) empty (add1 "error1"))]
          [else
           (if (empty? ys)
               (add1 "error2")
               (cons (cons (car xs) (car ys)) (zip (cdr xs) (cdr ys))))]))

  (define (unzip xs)
    (cond [(empty? xs) (cons empty empty)]
          [else
           (let ([rst (unzip (cdr xs))]
                 [hd (car xs)])
             (cons (cons (car hd) (car rst))
                   (cons (cdr hd) (cdr rst))))]))

  (define (make_list n)
    (if (< n 0)
        empty
        (cons (cons 0 0) (make_list (- n 1)))))
  
  (define (main n)
    (let ([xs (make_list n)])
      (let ([zs (unzip xs)])
        (zip (car zs) (cdr zs))))))

(require 'zip_unzip)
(main •)
