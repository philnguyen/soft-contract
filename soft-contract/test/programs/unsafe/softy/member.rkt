#lang racket
(require soft-contract/fake-contract)

(define (member x l)
  (if (empty? l) empty
      (if (equal? x (car l)) l (member x (cdr l)))))

(provide/contract
 [member (any/c #|HERE|# any/c . -> . (listof any/c))])
