#lang racket/base

(require (only-in "array-struct.rkt"
                    array?
                    array-shape
                    array-default-strict!
                    unsafe-array-proc
                    unsafe-build-array)
           (only-in "array-broadcast.rkt" array-broadcast array-shape-broadcast)
         (only-in "array-broadcast.rkt" array-broadcasting))

(provide mix)

;; -- array-pointwise

(require (for-syntax racket/base))
(define-syntax-rule (ensure-array name arr-expr)
  (let ([arr arr-expr])
    (if (array? arr) arr (raise-argument-error name "Array" arr))))

(define-syntax (inline-array-map stx)
  (syntax-case stx ()
    [(_ f arr-expr)
     (syntax/loc stx
       (let ([arr  (ensure-array 'array-map arr-expr)])
         (define ds (array-shape arr))
         (define proc (unsafe-array-proc arr))
         (define arr* (unsafe-build-array ds (λ (js) (f (proc js)))))
         (array-default-strict! arr*)
         arr*))]
    [(_ f arr-expr arr-exprs ...)
     (with-syntax ([(arrs ...)   (generate-temporaries #'(arr-exprs ...))]
                   [(procs ...)  (generate-temporaries #'(arr-exprs ...))])
       (syntax/loc stx
         (let ([arr   (ensure-array 'array-map arr-expr)]
               [arrs  (ensure-array 'array-map arr-exprs)] ...)
           (define ds (array-shape-broadcast (list (array-shape arr) (array-shape arrs) ...)))
           (let ([arr   (array-broadcast arr ds)]
                 [arrs  (array-broadcast arrs ds)] ...)
             (define proc  (unsafe-array-proc arr))
             (define procs (unsafe-array-proc arrs)) ...
             (define arr* (unsafe-build-array ds (λ (js) (f (proc js) (procs js) ...))))
             (array-default-strict! arr*)
             arr*))))]))

(define array-map
  (case-lambda
    [(f arr)  (inline-array-map f arr)]
    [(f arr0 arr1)  (inline-array-map f arr0 arr1)]))

;; A Weighted-Signal is a (List (Array Float) Real)

;; Weighted sum of signals, receives a list of lists (signal weight).
;; Shorter signals are repeated to match the length of the longest.
;; Normalizes output to be within [-1,1].

;; mix : Weighted-Signal * -> (Array Float)
(define (mix . ss)
  (define signals
    (for/list ([s ss])
      (car s)))
  (define weights
    (for/list ([x ss])
      (real->double-flonum (cadr x))))
  (define downscale-ratio (/ 1.0 (apply + weights)))
  ;; scale-signal : Float -> (Float -> Float)
  (define ((scale-signal w) x) (* x w downscale-ratio))
  (parameterize ([array-broadcasting 'permissive]) ; repeat short signals
    (for/fold ([res (array-map (scale-signal (car weights))
                               (car signals))])
        ([s (in-list (cdr signals))]
         [w (in-list (cdr weights))])
      (define scale (scale-signal w))
      (array-map (lambda (acc  ; : Float
                          new) ; : Float
                   (+ acc (scale new)))
                 res s))))
