#lang racket

(struct foo (x))

(provide (contract-out (foo-x (-> foo? integer?))))
