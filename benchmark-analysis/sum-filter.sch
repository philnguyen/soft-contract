(module filter ; opaque
  (provide [filter ([p? : (any . -> . any)] [_ : (listof any)] . -> . (listof (λ (y) (p? y))))]))

(module add-nums
  (provide [add-nums ((listof any) . -> . num?)])
  (require filter)
  
  (define (add-nums xs)
    (foldl + 0 (filter num? xs)))
  
  (define (foldl f z xs)
    (if (empty? xs) z (foldl f (f (car xs) z) (cdr xs)))))

(require add-nums)
(add-nums •)