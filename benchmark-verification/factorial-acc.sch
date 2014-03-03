(module factorial
  (provide
   [factorial (int? . -> . int?)])
  (define (factorial n)
    (factorial-acc n 1))
  (define (factorial-acc n acc)
    (if (zero? n) acc
        (factorial-acc (sub1 n) (* n acc)))))

(require factorial)
(factorial •)