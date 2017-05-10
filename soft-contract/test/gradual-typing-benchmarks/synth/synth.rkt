#lang racket/base

(provide
  fs
  sawtooth-wave
  seconds->samples
  emit)

(require (only-in "array-struct.rkt"
           array?
           array-shape
           unsafe-array-proc
           array-size
           array-strictness)
         (only-in racket/unsafe/ops unsafe-fx+ unsafe-fx<)
         (only-in "array-utils.rkt" next-indexes!)
         (only-in racket/math exact-floor))

;; --- from array-sequence.rkt

(require (for-syntax racket/base syntax/parse))
(define-sequence-syntax in-array
  (λ () #'in-array)
  (λ (stx)
    (syntax-case stx ()
      [[(x) (_ arr-expr)]
       (syntax/loc stx
         [(x)
          (:do-in
           ([(ds size dims js proc)
             (let ([arr  arr-expr])
               (cond [(array? arr)
                      (define ds (array-shape arr))
                      (define dims (vector-length ds))
                      (define size (array-size arr))
                      (define proc (unsafe-array-proc arr))
                      (define js (make-vector dims 0))
                      (values ds size dims js proc)]
                     [else
                      (raise-argument-error 'in-array "Array" arr)]))])
           (void)
           ([j 0])
           (unsafe-fx< j size)
           ([(x)  (proc js)])
           #true
           #true
           [(begin (next-indexes! ds dims js)
                   (unsafe-fx+ j 1))])])]
      [[_ clause] (raise-syntax-error 'in-array "expected (in-array <Array>)" #'clause #'clause)])))

;; -- synth

;; TODO this slows down a bit, it seems, but improves memory use
(array-strictness #f)

(define fs 44100)
(define bits-per-sample 16)

(define (freq->sample-period freq)
  (round (/ fs freq)))

(define (seconds->samples s)
  (inexact->exact (round (* s fs))))

;; --- Oscillators

;; array functions receive a vector of indices
(define-syntax-rule (array-lambda (i) body ...)
  (lambda (i*) (let ([i (vector-ref i* 0)]) body ...)))

(define ((make-sawtooth-wave coeff) freq)
  (define sample-period (freq->sample-period freq))
  (define sample-period/2 (quotient sample-period 2))
  (array-lambda (x)
    ;; gradually goes from -1 to 1 over the whole cycle
    (define x* (exact->inexact (modulo x sample-period)))
    (* coeff (- (/ x* sample-period/2) 1.0))))
(define sawtooth-wave         (make-sawtooth-wave 1.0))

;; --- Emit

;; assumes array of floats in [-1.0,1.0]
;; assumes gain in [0,1], which determines how loud the output is
(define (signal->integer-sequence signal #:gain [gain 1])
  (for/vector #:length (array-size signal)
              ([sample (in-array signal)])
    (max 0 (min (sub1 (expt 2 bits-per-sample)) ; clamp
                (exact-floor
                 (* gain
                    (* (+ sample 1.0) ; center at 1, instead of 0
                       (expt 2 (sub1 bits-per-sample)))))))))

;; `emit` used to write a file.
;; For now, it just converts a signal to a sequence.
(define (emit signal)
  (signal->integer-sequence signal #:gain 0.3))

