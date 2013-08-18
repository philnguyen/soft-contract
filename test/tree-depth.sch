(abbrev/c TREE/C (μ X (or/c (struct/c leaf ()) (struct/c node (X X)))))

(module tree-depth
  (provide [depth (TREE/C . -> . (and/c int? (>=/c 0)))])
  (struct leaf ())
  (struct node (l r))
  (define (depth t)
    (if (node? t) (+ 1 (max (depth (node-l t)) (depth (node-r t)))) 0))
  (define (max x y) (if (> x y) x y)))

(require tree-depth)
(depth •)