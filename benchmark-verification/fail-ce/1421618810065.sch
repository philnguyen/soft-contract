(module argmin racket
  (provide
    (contract-out
      [argmin ((any/c . -> . number?) (cons/c any/c (listof any/c)) . -> . any/c)]))

  ;; Produce the element that minimizes f
  (define (argmin f xs)
    (argmin/acc f (car xs) (f (car xs)) (cdr xs)))

  (define (argmin/acc f a b xs)
    (if (empty? xs)
        a
        (if (< b (f (car xs)))
            (argmin/acc f a b (cdr xs))
            (argmin/acc f (car xs) (f (car xs)) (cdr xs))))))
