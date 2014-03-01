(module sum
  (provide [sum ([n : int?] . -> . (and/c int? (>=/c n)))])
  (define (sum n)
    (if (<= n 0) 0
        (+ n (sum (- n 1))))))

(require sum)
(sum •)