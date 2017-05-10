#lang racket/base

(require
  (only-in "spreadsheet.rkt" rktd->spreadsheet)
  (only-in "summary.rkt" get-project-name from-rktd)
  (only-in "lnm-plot.rkt" lnm-plot)
)

;; Just testing

(define L-max 2)
(define NUM_SAMPLES 60)

(define (main filename)
  ;; Parse data from input file (also creates module graph)
  (define summary (from-rktd filename))
  (define name (get-project-name summary))
  (define l-list (for/list ([i (in-range (add1 L-max))]) i))
  ;; Create L-N/M pictures
  (define picts (lnm-plot summary #:L l-list
                                  #:N 3
                                  #:M 10
                                  #:max-overhead 20
                                  #:cutoff-proportion 0.6
                                  #:num-samples NUM_SAMPLES
                                  #:plot-height 300
                                  #:plot-width 400))
  ;; Make a spreadsheet, just to test that too
  (rktd->spreadsheet filename #:output "./test-case-output.out" #:format 'tab)
  (void)
)

;(time (main "../base/data/echo.rktd")) ;; 97ms
;(time (main "../base/data/sieve.rktd")) ;; 56ms
;(time (main "../base/data/gregor.rktd")) ;; 44640ms
(time (main "../base/data/suffixtree.rktd")) ;; 213ms
