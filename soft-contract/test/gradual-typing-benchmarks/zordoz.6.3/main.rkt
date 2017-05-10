#lang racket/base

(require benchmark-util)

(require "zo-shell.rkt")

;; Stress tests: search entire bytecode for the fairly-common branch struct
(define SELF-TEST '("../base/zo-shell.zo" "../base/zo-find.zo" "../base/zo-string.zo" "../base/zo-transition.zo"))
(define (self-test)
  (for ([b SELF-TEST]) (init (vector b "branch"))))

(define SMALL-TEST "../base/hello-world.zo")
(define (small-test)
  (init (vector SMALL-TEST "branch")))

(define LARGE-TEST "../base/streams.zo")
(define (large-test)
  (init (vector LARGE-TEST "branch")))

;; -----------------------------------------------------------------------------

(define-syntax-rule (main test)
  (with-output-to-file "/dev/null" test #:exists 'append))

(time (main self-test)) ; 1316ms
;(time (main small-test)) ;
;(time (main large-test)) ; 63ms
