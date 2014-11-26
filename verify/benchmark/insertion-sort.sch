(module opaque
  (provide [insert (integer? SORTED/C . -> . (and/c (nelistof integer?) ne-sorted?))]
           [ne-sorted? ((nelistof integer?) . -> . boolean?)]
           [SORTED/C any/c])
  (define SORTED/C (or/c empty? (and/c (nelistof integer?) ne-sorted?))))

(module insertion-sort
  (require opaque)
  (provide
   [sort (->i ([l (listof integer?)]) (res (l) (and/c SORTED/C (λ (r) (if (empty? l) (empty? r) (cons? r))))))])
  (define (sort xs) (foldl insert xs empty))
  (define (foldl f l b)
    (if (empty? l) b (foldl f (cdr l) (f (car l) b)))))

(require insertion-sort)
(sort •)
