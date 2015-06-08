(module filter racket ; opaque
  (provide/contract [filter (->i ([p? (any/c . -> . any/c)] [_ (listof any/c)])
				 (res (p? _) (listof (λ (y) (p? y)))))]))

(module add-nums racket
  (provide/contract [add-nums ((listof any/c) . -> . number?)])
  (require (submod ".." filter))
  
  (define (add-nums xs)
    (foldl + 0 xs))
  
  (define (foldl f z xs)
    (if (empty? xs) z (foldl f (f (car xs) z) (cdr xs)))))

(require 'add-nums)
(add-nums •)
