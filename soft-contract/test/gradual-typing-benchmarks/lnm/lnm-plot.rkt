#lang racket/base

;; Create L-N/M plots for .rktd files

;; Input:
;; - Raw experimental data (.rktd)
;;   (Optionally a list)
;; Output:
;; - Pict showing an L-N/M plot for the data
;;   (Or, a list of such plots)

(provide
  lnm-plot
)

;; -----------------------------------------------------------------------------

(require
  (only-in "bitstring.rkt"
    in-reach
    log2)
  (only-in "summary.rkt"
    all-variations
    from-rktd
    get-num-variations
    get-project-name
    predicate->variations
    untyped-mean
    variation->mean-runtime)
  plot/pict
  (only-in racket/math exact-floor)
  (only-in plot/utils linear-seq)
  (only-in racket/math exact-floor exact-ceiling)
  (only-in racket/stream stream-length stream->list stream-filter)
)

;; =============================================================================
;; --- constants

(define DEFAULT_N 3)
(define DEFAULT_M 10)
(define DEFAULT_XLIMIT 20)
(define DEFAULT_CUTOFF 0.6)
(define DEFAULT_SAMPLES 20)

(define THIN (* 1.2 (line-width)))
(define THICK (* 1.8 (line-width)))

;; -----------------------------------------------------------------------------
;; --- plotting

(define (lnm-plot summary
                  #:L L ;; (U Index (Listof Index)), L-values to plot
                  #:N [N DEFAULT_N]  ;; Index, recommened N limit
                  #:M [M DEFAULT_M] ;; Index, recommended M limit
                  #:max-overhead [xmax DEFAULT_XLIMIT] ;; Index, max. x-value
                  #:num-samples [num-samples DEFAULT_SAMPLES] ;; Index
                  #:cutoff-proportion [cutoff-proportion DEFAULT_CUTOFF] ;; Flonum, between 0 and 1.
                  #:plot-width [width (plot-width)] ;; Index
                  #:plot-height [height (plot-height)]) ;; Index
  (define L-list (or (and (list? L) L) (list L)))
  (define num-vars (get-num-variations summary))
  (define cutoff-point (* cutoff-proportion num-vars))
  ;; Make renderers for the lines
  (define N-line (vertical-line N #:y-max num-vars
                                  #:color 'forestgreen
                                  #:width THIN))
  (define M-line (vertical-line M #:y-max num-vars
                                  #:color 'goldenrod
                                  #:width THIN))
  (define cutoff-line (horizontal-line cutoff-point #:x-max xmax
                                                    #:color 'orangered
                                                    #:style 'short-dash
                                                    #:width THICK))
  ;; Get yticks
  (define yticks (compute-yticks num-vars 6 #:exact (list cutoff-point)))
  ;; Set plot parameters ('globally', for all picts)
  (parameterize (
    [plot-x-ticks (compute-xticks 5)]
    [plot-y-ticks (compute-yticks num-vars 6 #:exact cutoff-point)]
    [plot-x-far-ticks no-ticks]
    [plot-y-far-ticks no-ticks]
    [plot-font-face "bold"]
    [plot-font-size 16])
    ;; Create 1 pict for each value of L
    (for/list ([L (in-list L-list)])
      (define F (function (count-variations summary L #:cache-up-to xmax) 0 xmax
                          #:samples num-samples
                          #:color 'navy
                          #:width THICK))
      (plot-pict (list N-line M-line cutoff-line F)
                 #:x-min 0
                 #:x-max xmax
                 #:y-min 0
                 #:y-max num-vars
                 #:x-label "Overhead (vs. untyped)"
                 #:y-label "Count"
                 #:width width
                 #:height height))))

;; Return a function (-> Real Index) on argument `N`
;;  that counts the number of variations
;;  which can reach, in L or fewer steps,
;;  a variation with overhead no more than `N`
;; (: count-variations (-> Summary Index (-> Real Index)))
(define (count-variations sm L #:cache-up-to [lim #f])
  (define baseline (untyped-mean sm))
  (define cache (and lim (cache-init sm lim #:L L)))
  (lambda (N)
    (define good? (make-variation->good? sm (* N baseline) #:L L))
    (if (and cache (<= N lim))
        ;; Use cache to save some work, only test the variations
        ;; in the next bucket
        (cache-lookup cache N good?)
        ;; No cache, need to test all variations
        (stream-length (predicate->variations sm good?)))))

;; Make a predicate checking whether a variation is good.
;; Good = no more than `L` steps away from a variation
;;        with average runtime less than `good-threshold`.
(define (make-variation->good? summary good-threshold #:L [L 0])
  (lambda (var)
    (for/or ([var2 (cons var (in-reach var L))])
      (< (variation->mean-runtime summary var2)
         good-threshold))))

;; -----------------------------------------------------------------------------
;; -- cache

;; Create a cache that saves the configurations between discrete overhead values
(define (cache-init summary max-overhead #:L [L 0])
  (define base-overhead (untyped-mean summary))
  (define unsorted-variations (box (all-variations summary)))
  ;; For each integer-overhead-range [0, 1] [1, 2] ... [max-1, max]
  ;; save the variations within that overhead to a cache entry
  (for/vector ([i (in-range (add1 max-overhead))])
    (define good? (make-variation->good? summary (* i base-overhead) #:L L))
    (define-values (good-vars rest)
      (stream-partition good? (unbox unsorted-variations)))
    (set-box! unsorted-variations rest)
    (stream->list good-vars)))

;; Count the number of variations with running time less than `overhead`.
;; Use `test-fun` to manually check variations we aren't sure about
(define (cache-lookup $$$ overhead test-fun)
  (define lo-overhead (exact-floor overhead))
  (define hi-overhead (exact-ceiling overhead))
  (define num-known
    (for/sum ([i (in-range (add1 lo-overhead))])
      (length (vector-ref $$$ i))))
  (if (= hi-overhead lo-overhead)
      ;; Short circuit, because original overhead was an integer
      num-known
      ;; Else test all the variations in the "next" bucket
      (+ num-known
         (for/sum ([var (in-list (vector-ref $$$ hi-overhead))]
                   #:when (test-fun var)) 1))))

(define (stream-partition f stream)
  (define not-f (lambda (x) (not (f x))))
  (values (stream-filter f stream)
          (stream-filter not-f stream)))

;; -----------------------------------------------------------------------------
;; --- plotting utils

;; Compute `num-ticks` evenly-spaced y ticks between 0 and `max-y`.
;; Round all numbers down a little, except for numbers in the optional
;;  list `exact`.
;; TODO
(define (compute-yticks max-y num-ticks #:exact [exact '()])
  (define exact-list (or (and (list? exact) exact) (list exact)))
  (define round-y (if (< max-y 1000)
                      round
                      (lambda (n) (* 100 (exact-floor (/ n 100))))))
  (ticks (lambda (ax-min ax-max)
           (for/list ([y (in-list (linear-seq ax-min ax-max num-ticks))])
             (define rounded (round-y y))
             (define ex (findf (lambda (n) (= rounded (round-y n)))
                               exact-list))
             (pre-tick (or (and ex (round ex))
                           rounded)
                       #t)))
         (lambda (ax-min ax-max pre-ticks)
                 (for/list ([pt (in-list pre-ticks)])
                   (number->string (pre-tick-value pt))))))

(define (compute-xticks num-ticks)
  (ticks (lambda (ax-min ax-max)
           (for/list ([i (in-list (linear-seq 1 ax-max num-ticks))])
             (pre-tick (round i) #t)))
         (lambda (ax-min ax-max pre-ticks)
           (for/list ([pt (in-list pre-ticks)])
             (format "~ax" (pre-tick-value pt))))))

(define (horizontal-line y-val
                         #:x-min [x-min 0]
                         #:x-max [x-max 1]
                         #:color [c 'black]
                         #:width [w (line-width)]
                         #:style [s 'solid])
  (lines (list (list x-min y-val)
               (list x-max y-val))
         #:color c
         #:width w
         #:style s))

(define (vertical-line x-val
                       #:y-min [y-min 0]
                       #:y-max [y-max 1]
                       #:color [c 'black]
                       #:width [w (line-width)]
                       #:style [s 'solid])
  (lines (list (list x-val y-min)
               (list x-val y-max))
         #:color c
         #:width w
         #:style s))
