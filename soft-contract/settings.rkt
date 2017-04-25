#lang typed/racket/base

(provide (all-defined-out))
(require "utils/def.rkt")

(define-parameter debug-trace? : Boolean #f)
(define-parameter debug-iter? : Boolean #f)
