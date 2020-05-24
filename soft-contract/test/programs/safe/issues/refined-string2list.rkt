#lang racket

(define l1 (string->list "abc"))
(define l2 (string->list ""))

(provide
 (contract-out
  [l1 (and/c (listof char?) pair?)]
  [l2 null?]))
