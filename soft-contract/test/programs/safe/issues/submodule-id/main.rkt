#lang racket/base

(require "adapter.rkt")
(define boxed-x (my-box -3))
(displayln (absz (my-box-x boxed-x)))
