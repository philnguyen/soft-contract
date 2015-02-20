#lang racket
(require soft-contract/fake-contract)

(define (argmin f xs)
  (cond [(empty? (cdr xs)) (f (car xs))]
        [else (min (f (car xs))
                   (argmin f (cdr xs)))]))

(define (min x y)
  (if (< x y) x y))

(provide/contract
 [argmin ((-> any/c number?) (cons/c any/c (listof any/c)) . -> . any/c)])
