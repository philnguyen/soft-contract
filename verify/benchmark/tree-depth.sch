(module tree-depth racket
  (provide/contract
   [depth (TREE/C . -> . (and/c integer? (>=/c 0)))]
   [TREE/C any/c])
  (struct leaf ())
  (struct node (l r))
  (define (depth t)
    (if (node? t) (+ 1 (max (depth (node-l t)) (depth (node-r t)))) 0))
  (define (max x y) (if (> x y) x y))
  (define TREE/C (μ/c (X) (or/c (struct/c leaf) (struct/c node X X)))))

(require 'tree-depth)
(depth •)
