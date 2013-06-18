(module max
  (provide
   [max* (real? real? . ->* . real?)])
  (define (max a b)
    (if (>= a b) a b))
  (define* (max* x xs)
    (foldl max x xs))
  (define (foldl f z xs)
    (cond
      [(empty? xs) z]
      [else (foldl f (f (car xs) z) (cdr xs))])))

(require max)
(max* • • • • •)