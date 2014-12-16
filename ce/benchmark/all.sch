(module all
  (provide [all ((any/c . -> . any/c) (listof any/c) . -> . #|HERE|#boolean?)])
  (define (all p? xs)
    (cond
      [(empty? xs) #t]
      [(empty? (cdr xs)) (p? (car xs))]
      [else (and (p? (car xs)) (all p? (cdr xs)))])))

(require all)
(all • •)
