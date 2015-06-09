(module repeat racket
  (provide/contract
    [main (integer? . -> . (not/c false?))])
  (define (succ x) (+ x 1))
  (define (repeat f n s)
    (if (= n 0) s
        (f (repeat f (- n 1) s))))
  (define (main n)
    (> (repeat succ n 0) n)))
