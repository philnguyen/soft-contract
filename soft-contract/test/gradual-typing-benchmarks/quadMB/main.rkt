#lang racket/base

;; AKA quick-test.rkt

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 (only-in racket/class new send)
(only-in "world.rkt"
  world:allow-hyphenated-last-word-in-paragraph
  world:quality-default
  world:draft-quality)
(only-in "quad-main.rkt"
  typeset)
(only-in "quick-sample.rkt"
  quick-sample)
(only-in "render.rkt"
  ;; TODO worried about this signature
  pdf-renderer%))

;; =============================================================================

;; 137ms
(parameterize ([world:quality-default world:draft-quality])
  (time
    (begin
      (define to (typeset (quick-sample)))
      (send (new pdf-renderer%) render-to-file to "./output.pdf")
      (void))))
;; 630ms for heart-of-darkness
