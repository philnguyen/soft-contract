#lang racket

(define (length l)
  (if (null? l) 0 (+ 1 (length (cdr l)))))

(define (map f xs)
  (match xs
    ['() null]
    [(cons x xs*) (cons (f x) (map f xs*))]))

(define (append xs ys)
  (if (null? xs)
      ys
      (cons (car xs) (append (cdr xs) ys))))

(define/contract append-assoc
  (->i ([Xs list?]
        [Ys list?]
        [Zs list?])
       (_ {Xs Ys Zs} (λ (_) (equal? (append Xs (append Ys Zs))
                                    (append (append Xs Ys) Zs)))))
  (λ (xs ys zs)
    (if (null? ys)
        'trivial
        (append-assoc xs (cdr ys) zs))))

(provide
 (contract-out
  [append-assoc (list? list? list? . -> . any/c)]))
