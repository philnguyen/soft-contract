#lang racket
(struct foo (x))
(define foo/c (struct/c foo (-> (recursive-contract foo/c))))
