#lang racket

(define (sorted? l)
  (match l
    ['() #t]
    [(list _) #t]
    [(cons x1 (and xs (cons x2 _)))
     (and (<= x1 x2) (sorted? xs))]))

(define (insert x xs)
  (match xs
    ['() (list x)]
    [(cons x1 xs*) (if (<= x x1) (cons x xs) (cons x1 (insert x xs*)))]))

(define (insertion-sort xs)
  (match xs
    ['() '()]
    [(list x) xs]
    [(cons x xs*) (insert x (insertion-sort xs*))]))

(define/contract insert-preserves-sortedness
  (->i ([X real?]
        [Xs (listof real?)]
        [sorted {Xs} (λ (_) (sorted? Xs))])
       (_ {X Xs} (λ (_) (sorted? (cons X Xs)))))
  (λ (x xs _)
    (match xs
      ['() 'trivial]
      [(cons x1 xs*) (if (<= x x1)
                         'trivial
                         (insert-preserves-sortedness x xs*))])))

(define/contract insertion-sort-sorts
  (->i ([Xs (listof real?)])
       (_ {Xs} (λ (_) (sorted? (insertion-sort Xs)))))
  (λ (xs)
    (match xs
      ['() 'trivial]
      [(list x) 'trivial]
      [(cons x xs*)
       (insertion-sort-sorts xs*)
       (insert-preserves-sortedness x xs*)])))

(provide
 (contract-out
  [insert-preserves-sortedness
   (->i ([X real?]
         [Xs (listof real?)]
         [sorted {Xs} (λ (_) (sorted? Xs))])
        (_ {X Xs} (λ (_) (sorted? (cons X Xs)))))]))
