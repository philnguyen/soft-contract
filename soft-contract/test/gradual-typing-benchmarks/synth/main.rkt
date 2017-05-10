#lang racket/base

(require (only-in "sequencer.rkt" note sequence)
         (only-in "drum.rkt" drum)
         (only-in "mixer.rkt" mix)
         (only-in "synth.rkt" emit sawtooth-wave))

(require (for-syntax racket/base syntax/parse) racket/stxparam)

(begin-for-syntax
 (define-syntax-class mixand
   #:attributes (signal weight)
   (pattern [signal:expr (~datum #:weight) weight:expr])
   (pattern signal:expr #:with weight #'1)))

(define-syntax (mix/sugar stx)
  (syntax-parse stx
    [(_ sig:mixand ...)
     #'(mix (list sig.signal sig.weight) ...)]))

;; Test from Vincent's repo.
(define (large-test)
 (emit
  (mix/sugar
   (sequence 2 (list
     (note 'C 5 1)
     (cons #f 1)
     (note 'C 5 1)
     (cons #f 1)
     (note 'A# 4 1)
     (cons #f 1)
     (note 'C 5 1)
     (cons #f 3)
     (note 'G 4 1)
     (cons #f 3)
     (note 'G 4 1)
     (cons #f 1)
     (note 'C 5 1)
     (cons #f 1)
     (note 'F 5 1)
     (cons #f 1)
     (note 'E 5 1)
     (cons #f 1)
     (note 'C 5 1)
     (cons #f 9))
     380 sawtooth-wave)
   (drum 8 '(O #f #f #f X #f #f #f) 380))))

;; Small test, for development
(define (small-test)
 (emit
  (mix/sugar
   (sequence 1 (list
     (note 'C 5 1)
     (cons #f 1)
     (note 'C 5 1))
     1200 sawtooth-wave)
    (drum 1 '(O #f #f #f X) 1200))))

(define (mid-test)
  (emit
   (mix/sugar
    (sequence 1 (list
      (note 'D 0 1)
      (note 'D 5 1)
      (cons #f 1)
      (note 'D 3 1)
      (note 'D 8 1)
      (cons #f 1)
      (note 'D 5 1)
      (note 'D 10 1)
      (cons #f 1)
      (note 'D 0 1)
      (note 'D 5 1)
      (cons #f 1)
      (note 'D 3 1)
      (note 'D 8 1)
      (cons #f 1)
      (note 'D 6 1)
      ;; (note 'D 11 1)
      (cons #f 1)
      (note 'D 5 1)
      (note 'D 10 1)
      (cons #f 2)
      (note 'D 0 1)
      (note 'D 5 1)
      (cons #f 1)
      (note 'D 3 1)
      (note 'D 8 1)
      (cons #f 1)
      (note 'D 5 1)
      (note 'D 10 1)
      (cons #f 1)
      (note 'D 3 1)
      (note 'D 8 1)
      (cons #f 1)
      (note 'D 0 1)
      (note 'D 5 1))
              1200 sawtooth-wave)
    (drum 1 '(O #f X #f O #f X #f O #f X #f O O X X) 360))))

(define (main)
  ;; (mid-test) ;; 70ms
  (large-test) ;; 170ms
  ;; (small-test) ;; 7ms
  (void))

(time (main))
