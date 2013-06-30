(module with-many
  (provide
   [with-many
    ((any (any . -> . any) . -> . any) (listof any) ((listof any) . -> . any) . -> . any)])
  (define (with-many wf l f)
    (cond
      [(empty? l) (f l)]
      [else (let ([x (car l)]
                  [xs (cdr l)])
              (wf x (λ (x1) (with-many wf xs (λ (xs1) (f (cons x1 xs1)))))))])))

(require with-many)
(with-many • • •)