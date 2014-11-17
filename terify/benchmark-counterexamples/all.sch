(module all
  (provide [all ((any . -> . any) (listof any) . -> . #|HERE|#bool?)])
  (define (all p? xs)
    (cond
      [(empty? xs) #t]
      [(empty? (cdr xs)) (p? (car xs))]
      [else (and (p? (car xs)) (all p? (cdr xs)))])))

(require all)
(all • •)
