(module recursive-div2
  (provide
   [recursive-div2 ((μ/c (X) (or/c empty? (cons/c any/c (cons/c any/c X))))
                    . -> . (listof any/c))])
  (define (recursive-div2 l)
    (if (empty? l) empty
        (cons (car l) (recursive-div2 (cdr (cdr l)))))))

(require recursive-div2)
(recursive-div2 •)
