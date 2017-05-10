#lang racket/base

(require (only-in "array-struct.rkt" build-array)
         (only-in "array-transform.rkt" array-append*)
         (only-in "synth.rkt" fs)
         (only-in "mixer.rkt" mix))

(provide sequence note)

;; details at http://www.phy.mtu.edu/~suits/notefreqs.html
(define (note-freq note)
  ;; A4 (440Hz) is 57 semitones above C0, which is our base.
  (* 440 (expt (expt 2 1/12) (- note 57)))) 

;; A note is represented using the number of semitones from C0.
(define (name+octave->note name octave)
  (+ (* 12 octave)
     (case name
       [(C) 0] [(C# Db) 1] [(D) 2] [(D# Eb) 3]  [(E) 4] [(F) 5] [(F# Gb) 6]
       [(G) 7] [(G# Ab) 8] [(A) 9] [(A# Bb) 10] [(B) 11])))

;; Single note.
(define (note name octave duration)
  (cons (name+octave->note name octave) duration))

;; Accepts notes or pauses, but not chords.
(define (synthesize-note note n-samples function)
  (build-array (vector n-samples)
               (if note
                   (function (note-freq note))
                   (lambda (x) 0.0)))) ; pause

;; repeats n times the sequence encoded by the pattern, at tempo bpm
;; pattern is a list of either single notes (note . duration) or
;; chords ((note ...) . duration) or pauses (#f . duration)
(define (sequence n pattern tempo function)
  (define samples-per-beat (quotient (* fs 60) tempo))
  (array-append*
   (for*/list ([i    (in-range n)] ; repeat the whole pattern
               [note (in-list  pattern)])
     (define nsamples (* samples-per-beat (cdr note)))
     (if (list? (car note)) ; chord
         (apply mix
                (for/list ([x (in-list (car note))])
                  (list (synthesize-note x nsamples function)
                        1))) ; all of equal weight
         (synthesize-note (car note) nsamples function)))))
