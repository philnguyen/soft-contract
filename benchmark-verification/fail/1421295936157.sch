(module len racket
  #;(provide 
   (contract-out 
    [len ((listof any/c) . -> . (and/c integer? (lambda (n) (>= n 0))))]))
         	
  (define (len ls)
    (if (empty? ls) 0 (+ 1 (len (rest ls))))))
