#lang racket
(require "lib.rkt")

(define n (f 42))
(if (zero? n) 1 (/ 1 n))
