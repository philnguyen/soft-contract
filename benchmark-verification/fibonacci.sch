(module fib
  (provide
   [fib (int? . -> . int?)])
  (define (fib n)
    (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))

(require fib)
(fib •)