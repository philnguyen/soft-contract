#lang racket/base

(require (only-in "zo-shell.rkt" init))

;; Stress tests: search entire bytecode for the fairly-common branch struct
(define SELF-TEST '("../base/zo-shell.zo" "../base/zo-find.zo" "../base/zo-string.zo" "../base/zo-transition.zo"))
(define (self-test)
  (for ([b SELF-TEST]) (init (vector b "branch"))))

(define SMALL-TEST "../base/hello-world.zo")
(define (small-test)
  (init (vector SMALL-TEST "branch")))

(define LARGE-TEST "../base/large-test.zo")
(define (large-test)
  (init (vector LARGE-TEST "branch")))

;; -----------------------------------------------------------------------------

(define-syntax-rule (main test)
  (with-output-to-file "/dev/null" test #:exists 'append))

(time (main self-test)) ; 310ms
;(time (main small-test)) ; 6ms
;(time (main large-test)) ; 20000ms
