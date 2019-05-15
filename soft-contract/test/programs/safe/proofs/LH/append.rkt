#lang racket

(define auto (λ _ 'trivial))

;; Source
;; https://github.com/ucsd-progsys/liquidhaskell/blob/develop/benchmarks/popl18/ple/pos/Append.hs

(define append
  (match-lambda**
   [('()         ys) ys]
   [((cons x xs) ys) (cons x (append xs ys))]))

(define map
  (match-lambda**
   [(f '()        ) '()]
   [(f (cons x xs)) (cons (f x) (map f xs))]))

(define concat-map
  (match-lambda**
   [(f '()        ) '()]
   [(f (cons x xs)) (append (f x) (concat-map f xs))]))

(define concatt
  (match-lambda
    ['()         '()]
    [(cons x xs) (append x (concatt xs))]))

(define/contract prop:append-neutral
  ;; FIXME parametric contract
  (->i ([xs list?])
       (_ {xs} (λ (_) (equal? (append xs '()) xs))))
  (match-lambda
    ['() 'trivial]
    [(cons _ xs) (prop:append-neutral xs)]))

(define/contract prop:append-assoc
  ;; FIXME parametric contract
  (->i ([xs list?]
        [ys list?]
        [zs list?])
       (_ {xs ys zs} (λ (_) (equal? (append (append xs ys) zs)
                                    (append xs (append ys zs))))))
  (λ (xs ys zs)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (prop:append-assoc xs* ys zs)])))

(define/contract prop:map-append
  ;; FIXME parametric contract
  (->i ([f (any/c . -> . any/c)]
        [xs list?]
        [ys list?])
       (_ {f xs ys} (λ (_) (equal? (map f (append xs ys))
                                   (append (map f xs) (map f ys))))))
  (λ (f xs ys)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (prop:map-append f xs* ys)])))

(define/contract prop:concat-map
  ;; FIXME parametric contract
  (->i ([f (any/c . -> . (listof list?))]
        [xs list?])
       (_ {f xs} (λ (_) (equal? (concatt (map f xs))
                                (concat-map f xs)))))
  (λ (f xs)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (prop:concat-map f xs*)])))

(provide
 (contract-out
  [prop:append-neutral
   ;; FIXME parametric contract
   (->i ([xs list?])
        (_ {xs} (λ (_) (equal? (append xs '()) xs))))]
  [prop:append-assoc
   ;; FIXME parametric contract
   (->i ([xs list?]
         [ys list?]
         [zs list?])
        (_ {xs ys zs} (λ (_) (equal? (append (append xs ys) zs)
                                     (append xs (append ys zs))))))]
  [prop:map-append
   ;; FIXME parametric contract
   (->i ([f (any/c . -> . any/c)]
         [xs list?]
         [ys list?])
        (_ {f xs ys} (λ (_) (equal? (map f (append xs ys))
                                    (append (map f xs) (map f ys))))))]
  [prop:concat-map
   ;; FIXME parametric contract
   (->i ([f (any/c . -> . (listof list?))]
         [xs list?])
        (_ {f xs} (λ (_) (equal? (concatt (map f xs))
                                 (concat-map f xs)))))]))
