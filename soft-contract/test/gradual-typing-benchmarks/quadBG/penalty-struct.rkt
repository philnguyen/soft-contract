#lang racket/base

;; For wrap.rkt

(provide (struct-out $penalty))

;; =============================================================================

(struct $penalty
  (hyphens ;: Natural]
   width   ;: Float]
) #:transparent)

