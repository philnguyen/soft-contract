(module sqr racket
  (define (positive? n) (> n 0))
  
  (define (sqr n) (* n n))
  
  (provide 
   (contract-out
    [sqr (integer? . -> . (and/c integer? positive?))]
    [positive? (real? . -> . boolean?)])))
  


