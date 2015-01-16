(module factorial racket
  (define (fact x)
    (if (zero? x)
        1
        (* x (fact (sub1 x)))))

  (provide
   (contract-out
    [fact (-> (>=/c 0) (and/c integer? (>=/c 0)))])))
