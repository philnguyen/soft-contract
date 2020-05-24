#lang racket

(struct foo (x))
(define leak (foo 'foo))

(provide (contract-out (foo-x (-> foo? integer?))
                       (leak foo?)))
