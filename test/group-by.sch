(module group-by
  (provide [group-by ((any any . -> . bool?) (listof any) . -> . (nelistof (listof any)))])
  (define (group-by =? xs)
    (if (empty? xs) (cons empty empty)
        (let ([x1 (car xs)]
              [xr (cdr xs)])
          (let* ([acs (group-by =? xr)]
                 [ac1 (car acs)]
                 [acr (cdr acs)])
            (if (or (empty? ac1) (=? x1 (car ac1)))
                (cons (cons x1 ac1) acr)
                (cons (cons x1 empty) acs)))))))

(require group-by)
(group-by • •)