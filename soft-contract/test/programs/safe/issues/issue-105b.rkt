#lang racket
;; struct-access-1.rkt

(struct foo (x))

(provide (contract-out (struct foo ((x exact-integer?)))))
