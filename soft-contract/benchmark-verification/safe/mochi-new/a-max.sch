(module a-max racket
  (provide/contract
   [main (integer? integer? . -> . (not/c false?))])
  
  (define (make_array n)
    (λ (i) (- n i)))

  (define (array_max n i a m)
    (cond [(>= i n) m]
          [else
           (let* ([x (a i)]
                  [z (if (> x m) x m)])
             (array_max n (+ 1 i) a z))]))

  (define (main n i)
    (cond [(and (> n 0) (>= i 0) (<= i 0))
           (let ([m (array_max n i (make_array n) -1)])
             (>= m n))]
          [else #t])))

(require 'a-max)
(main • •)
