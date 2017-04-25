#lang racket
(require soft-contract/fake-contract)

(define (f input extra)
  (cond
   [(and (number? input) (number? (car extra)))
    (+ input (car extra))]
   [(number? (car extra))
    (+ (string-length input) (car extra))]
   [else 0]))

(provide/contract
 [f ([or/c number? string?] cons? . -> . number?)])
