#lang racket/base

;; For wrap.rkt

(provide (struct-out $penalty))

;; =============================================================================

(struct $penalty
  (hyphens
   width) #:transparent)

