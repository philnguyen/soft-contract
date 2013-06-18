(module bt
  (provide
   [struct node ([left (μ X (or/c false? (struct/c node [X any X])))]
                 [data any]
                 [right (μ X (or/c false? (struct/c node [X any X])))])]
   [clone ((μ X (or/c false? (struct/c node [X any X])))
           . -> . (μ X (or/c false? (struct/c node [X any X]))))]
   [leaves# ((μ X (or/c false? (struct/c node [X any X]))) . -> . int?)])
  
  (struct node (left data right))
  
  (define (tree-id t)
    (if (false? t) #f
        (node (clone (node-left t)) (node-data t) (clone (node-right t)))))
  
  (define (leaves# t)
    (if (false? t) 0
        (add1 (+ [leaves# (node-left t)] [leaves# (node-right t)])))))

(require bt)
(leaves# (clone •))