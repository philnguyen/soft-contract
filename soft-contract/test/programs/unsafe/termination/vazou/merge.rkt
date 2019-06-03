#lang racket/base

(require racket/match
         soft-contract/fake-contract)

(define merge
  (match-lambda**
   [((cons x xs) (cons y ys))
    (cond [(< x y) (cons x (merge xs (cons y ys)))]
          [else (cons y (merge (cons x xs) #|HERE|# (cons y ys)))])]
   [('() ys) ys]
   [(xs _) xs]))

(provide
 (contract-out
  [merge ((listof real?) (listof real?) . -> . (listof real?) #:total? #t)]))
