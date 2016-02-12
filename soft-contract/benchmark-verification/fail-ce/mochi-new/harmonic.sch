(module harmonic racket
  (provide/contract
   [harmonic (integer? . -> . any/c)])
  
  (define (fold_left f acc xs)
    (cond [(empty? xs) acc]
          [else (fold_left f (f acc (car xs)) (cdr xs))]))
  
  (define (range i j)
    (cond [(> i j) empty]
          [else (cons i (range (+ 1 i) j))]))

  (define (harmonic n)
    (let ([ds (range #|HERE|# 0 n)])
      (fold_left (λ (s k) (+ s (/ 10000 k))) 0 ds))))

(require 'harmonic)
(harmonic •)
