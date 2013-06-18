(module opaque
  (require sorted?)
  (provide
   [insert (int? (and/c (listof int?) sorted?) . -> . (and/c (listof int?) sorted?))]
   [nums (listof int?)]))

(module insertion-sort
  (require opaque sorted?)
  (provide
   [sort ((listof int?) . -> . (and/c (listof int?) sorted?))])
  (define (sort xs)
    (foldl insert xs empty))
  (define (foldl f l b)
    (if (empty? l) b
        (foldl f (cdr l) (f (car l) b)))))

(module sorted?
  (provide
   [sorted? ((listof int?) . -> . any)])
  (define (sorted? xs)
    (or (empty? xs)
        (empty? (cdr xs))
        (and (< (car xs) (car (cdr xs)))
             (sorted? (cdr xs))))))

(require insertion-sort opaque)
(sort nums)