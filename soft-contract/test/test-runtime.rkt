#lang racket/base

(module+ test
  (require rackunit "../utils.rkt" "../lang.rkt" "../runtime.rkt")

  ;; Test smart application
  (check-equal? (-?@ 'false? (list (-@ 'false? (list (-x 'x)) '†)))
                (-x 'x))
  (check-equal? (-?@ -car (list (-@ -cons (list (-b 1) (-x 'x)) '†)))
                (-b 1))
  (let ([e (-@ '+ (list (-x 'x) (-x 'y)) '†)])
    (check-equal? (-?@ -cons (list (-@ -car (list e) '†) (-@ -cdr (list e) '†)))
                  e)
    (check-equal? (-?@ -cons (list (-@ -cdr (list e) '†) (-@ -car (list e) '†)))
                  (-@ -cons (list (-@ -cdr (list e) '†) (-@ -car (list e) '†)) 'Λ))))
