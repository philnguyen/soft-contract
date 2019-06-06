#lang racket

(require soft-contract/fake-contract)

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

(define prop:map-preserves-length
  (->i ([F (any/c . -> . any/c #:total? #t)]
        [Xs list?])
       (_ {F Xs} (λ (_) (equal? (length Xs) (length (map F Xs)))))
       #:total? #t))
(define/contract map-preserves-length
  prop:map-preserves-length
  (λ (h zs)
    (match zs
      ['() 'trivial]
      [(cons _ zs*) (map-preserves-length h zs*)])))

(define prop:append-assoc
  (->i ([Xs list?]
        [Ys list?]
        [Zs list?])
       (_ {Xs Ys Zs} (λ (_) (equal? (append Xs (append Ys Zs))
                                    (append (append Xs Ys) Zs))))
       #:total? #t))
(define/contract append-assoc
  prop:append-assoc
  (λ (xs ys zs)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (append-assoc xs* ys zs)])))

(define prop:map-append
  (->i ([F (any/c . -> . any/c #:total? #t)]
        [Xs list?]
        [Ys list?])
       (_ {F Xs Ys} (λ (_) (equal? (map F (append Xs Ys))
                                   (append (map F Xs) (map F Ys)))))
       #:total? #t))
(define/contract map-append
  prop:map-append
  (λ (f xs ys)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (map-append f xs* ys)])))

(define prop:length-append
  (->i ([Xs list?]
        [Ys list?])
       (_ {Xs Ys} (λ (_) (equal? (+ (length Xs) (length Ys))
                                 (length (append Xs Ys)))))))
(define/contract length-append
  prop:length-append
  (λ (xs ys)
    (if (null? xs)
        'trivial
        (length-append (cdr xs) ys))))

(provide
 (contract-out
  [map-preserves-length prop:map-preserves-length]
  [append-assoc prop:append-assoc]
  [map-append prop:map-append]
  #;[length-append (list? list? . -> . any/c)]))
