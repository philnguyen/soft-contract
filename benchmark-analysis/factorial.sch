(module factorial
  (provide
   [factorial (int? . -> . int?)])
  (define (factorial n)
    (if (zero? n) 1 (* n (factorial (sub1 n))))))

(require factorial)
(factorial •)