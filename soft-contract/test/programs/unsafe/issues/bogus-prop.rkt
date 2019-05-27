#lang racket

(define (append l r)
  (cond [(null? l) r]
        [else (cons (car l) (append (cdr l) r))]))

(define (reverse xs)
  (cond [(null? xs) '()]
        [else (append (reverse (cdr xs)) (list (car xs)))]))

(define (thm-rev-app L R) (if (null? L) 'trivial-base 'trivial-ind))

(provide
 (contract-out
  [thm-rev-app (->i ([Xs list?] [Ys list?])
                    (_ {Xs Ys}
                       (λ (_)
                         (reverse (append Xs Ys))
                         (null? (reverse Xs)))))]))
