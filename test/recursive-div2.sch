(module recursive-div2
  (provide
   [recursive-div2 ((μ X (or/c empty? (cons/c any (cons/c any X))))
                    . -> . (listof any))])
  (define (recursive-div2 l)
    (if (empty? l) empty
        (cons (car l) (recursive-div2 (cdr (cdr l)))))))

(require recursive-div2)
(recursive-div2 •)