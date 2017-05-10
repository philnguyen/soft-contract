#lang racket/base

(require (only-in "array-struct.rkt"
                  array-size
                  make-array
                  build-array
                  unsafe-vector->array)
         (only-in "array-utils.rkt"
                  array-shape-size
                  check-array-shape)
         (only-in "array-transform.rkt" array-append*)
         (only-in "synth.rkt" fs seconds->samples)
         "data.rkt")

(provide drum)

;; -- drum

(define (random-sample) (- (* 2.0 (random)) 1.0))

;; Drum "samples" (Arrays of floats)
(define bass-drum
  (let ()
    ;; 0.05 seconds of noise whose value changes every 12 samples
    (define n-samples           (seconds->samples 0.05))
    (define n-different-samples (quotient n-samples 12))
    (define ds* (vector n-samples))
    (define ds
      (check-array-shape ds*
                         (λ () (raise-argument-error 'name "Indexes" ds))))
    (define vs
      (for/vector
                  #:length (array-shape-size ds)
                  #:fill 0.0
                  ([i      (in-range n-different-samples)]
                   [sample (in-producer random-sample)]
                   #:when #t
                   [j      (in-range 12)])
                  sample))
    (unsafe-vector->array ds vs)))

(define snare
  ;; 0.05 seconds of noise
  (build-array (vector (seconds->samples 0.05))
               (lambda (x) (random-sample))))

;; limited drum machine
;; drum patterns are simply lists with either O (bass drum), X (snare) or
;; #f (pause)
(define (drum n pattern tempo)
  (define samples-per-beat (quotient (* fs 60) tempo))
  (define (make-drum drum-sample samples-per-beat)
    (array-append*
     (list drum-sample
           (make-array (vector (- samples-per-beat
                                  (array-size drum-sample)))
                       0.0))))
  (define O     (make-drum bass-drum samples-per-beat))
  (define X     (make-drum snare     samples-per-beat))
  (define pause (make-array (vector samples-per-beat) 0.0))
  (array-append*
   (for*/list ([i    (in-range n)]
               [beat (in-list pattern)])
     (case beat
       ((X)  X)
       ((O)  O)
       ((#f) pause)))))
