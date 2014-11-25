(module filter ; opaque
  (provide [filter (->i ([p? (any/c . -> . any/c)] [_ (listof any/c)])
			(res (p? _) (listof (λ (y) (p? y)))))]))

(module add-nums
  (provide [add-nums ((listof any/c) . -> . number?)])
  (require filter)
  
  (define (add-nums xs)
    (foldl + 0 (filter number? xs)))
  
  (define (foldl f z xs)
    (if (empty? xs) z (foldl f (f (car xs) z) (cdr xs)))))

(require add-nums)
(add-nums •)
