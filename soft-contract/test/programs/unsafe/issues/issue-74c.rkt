#lang racket

(apply (λ (x y u t . z) (+ x y (length z))) (list 1 2 3))
