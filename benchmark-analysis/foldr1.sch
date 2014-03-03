(module foldr1
  (provide [foldr1 ((any any . -> . any) (nelistof any) . -> . any)])
  (define (foldr1 f xs)
    (let ([z (car xs)]
          [zs (cdr xs)])
      (if (empty? zs) z
          (f z (foldr1 f zs))))))

(require foldr1)
(foldr1 • •)