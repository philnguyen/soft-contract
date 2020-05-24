#lang racket/base
(provide with-syntax-source)
(require racket/contract)

(define/contract (with-syntax-source src stx)
  (syntax? any/c . -> . syntax?)
  (datum->syntax src
                 (if (syntax? stx) (syntax-e stx) stx)
                 (list (syntax-source src)
                       (syntax-line src)
                       (syntax-column src)
                       (syntax-position src)
                       (syntax-span src))))
