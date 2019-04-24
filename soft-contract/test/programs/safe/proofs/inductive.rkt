#lang racket

(define (length l)
  (if (null? l) 0 (+ 1 (length (cdr l)))))

(define (map f xs)
  (match xs
    ['() null]
    [(cons x xs*) (cons (f x) (map f xs*))]))

(define (append xs ys)
  (match xs
    ['() ys]
    [(cons x xs*) (cons x (append xs* ys))]))

(define/contract map-preserves-length
  (->i ([F (any/c . -> . any/c)]
        [Xs list?])
       (_ {F Xs} (λ (_) (equal? (length Xs) (length (map F Xs))))))
  (λ (h zs)
    (match zs
      ['() 'trivial]
      [(cons _ zs*) (map-preserves-length h zs*)])))

(define/contract append-assoc
  (->i ([Xs list?]
        [Ys list?]
        [Zs list?])
       (_ {Xs Ys Zs} (λ (_) (equal? (append Xs (append Ys Zs))
                                    (append (append Xs Ys) Zs)))))
  (λ (xs ys zs)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (append-assoc xs* ys zs)])))

(define/contract map-append
  (->i ([F (any/c . -> . any/c)]
        [Xs list?]
        [Ys list?])
       (_ {F Xs Ys} (λ (_) (equal? (map F (append Xs Ys))
                                   (append (map F Xs) (map F Ys))))))
  (λ (f xs ys)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (map-append f xs* ys)])))

#;(define/contract length-append
  (->i ([Xs list?]
        [Ys list?])
       (_ {Xs Ys} (λ (_) (equal? (+ (length Xs) (length Ys))
                                 (length (append Xs Ys))))))
  (λ (xs ys)
    (if (null? xs)
        'trivial
        (length-append (cdr xs) ys))))

(provide
 (contract-out
  [map-preserves-length ((any/c . -> . any/c) list? . -> . any/c)]
  [append-assoc (list? list? list? . -> . any/c)]
  [map-append ((any/c . -> . any/c) list? list? . -> . any/c)]
  #;[length-append (list? list? . -> . any/c)]))
