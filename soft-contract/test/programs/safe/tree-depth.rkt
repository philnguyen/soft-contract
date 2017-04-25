#lang racket
(require soft-contract/fake-contract)

(struct leaf ())
(struct node (l r))
(define (depth t)
  (if (node? t) (+ 1 (max (depth (node-l t)) (depth (node-r t)))) 0))
(define (max x y) (if (> x y) x y))
(define TREE/C (or/c (struct/c leaf)
                     (struct/c node
                               (recursive-contract TREE/C #:flat)
                               (recursive-contract TREE/C #:flat))))

(provide/contract
 [depth (TREE/C . -> . (and/c integer? (>=/c 0)))]
 [TREE/C any/c])
