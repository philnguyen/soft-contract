#lang racket
(require soft-contract/fake-contract)

(define (len xs)
  (if (empty? xs) 0
      (+ 1 (len (cdr xs)))))

(provide/contract
 [len (->i ([l #|HERE|# any/c]) (res (l) (and/c integer? (>=/c 0))))])
