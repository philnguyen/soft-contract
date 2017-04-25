#lang racket

(define (deriv a)
  (cond ((not (pair? a))
         (if (eq? a 'x) 1 0))
        ((eq? (car a) '+)
         (cons '+
               (map deriv (cdr a))))
        ((eq? (car a) '-)
         (cons '-
               (map deriv (cdr a))))
        ((eq? (car a) '*)
         (list '*
               a
               (cons '+
                     (map (lambda (a) (list '/ (deriv a) a)) (cdr a)))))
        ((eq? (car a) '/)
         (list '-
               (list '/
                     (deriv (cadr a))
                     (caddr a))
               (list '/
                     (cadr a)
                     (list '*
                           (caddr a)
                           (caddr a)
                           (deriv (caddr a))))))
        (else
         (add1 "should not reach here"))))

(define expr/c
  (or/c (not/c pair?)
        (list/c (one-of/c '+ '- '* '/)
                (recursive-contract expr/c)
                (recursive-contract expr/c))))

(provide
 (contract-out
  [deriv (expr/c . -> . any/c)]))
