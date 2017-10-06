#lang racket/base
#|  _    ____  ___   ______________________  _   _____    __ 
   | |  / / / / / | / / ____/_  __/  _/ __ \/ | / /   |  / / 
   | | / / / / /  |/ / /     / /  / // / / /  |/ / /| | / /  
   | |/ / /_/ / /|  / /___  / / _/ // /_/ / /|  / ___ |/ /___
   |___/\____/_/ |_/\____/ /_/ /___/\____/_/ |_/_/  |_/_____/
       ____________________________  ____  _____
      / ____/ ____/ ____/_  __/ __ \/ __ \/ ___/
     / /_  / __/ / /     / / / / / / /_/ /\__ \ 
    / __/ / /___/ /___  / / / /_/ / _, _/___/ / 
   /_/   /_____/\____/ /_/  \____/_/ |_|/____/               
   Persistent Functional Vectors.
   Copyright (c) 2011 David Van Horn
   Licensed under the Academic Free License version 3.0
  
   (at dvanhorn (dot ccs neu edu))
   Vucking vast vunctional fectors.
   Based on Conchon and Filliaˆtre, ML Workshop 2007,
   which is based on Baker, CACM 1978.
|#

#|
   This library enjoys:
      * thread safety,
      * disjointness, and
      * extensional equality.
|#
(require racket/match
         racket/include
         soft-contract/fake-contract)

;; TODO re-enable thread-safe stuff
#;(define s (make-semaphore 1))
(define (atomic th)
  (begin #;(semaphore-wait s)
         (begin0 (th)
                 #;(semaphore-post s))))

;; Like a box, but different.
(struct box (v) 
        #:mutable
        #:property prop:equal+hash
        (list
         (λ (f1 f2 equal?)
           (reroot! f1)
           (reroot! f2)
           (equal? (unbox f1) (unbox f2)))
         (λ (f equal-hash-code)
           (reroot! f)
           (equal-hash-code (unbox f)))
         (λ (f equal-hash-code)
           (reroot! f)
           (equal-hash-code (unbox f)))))

(define (set-box! fb x) (set-box-v! fb x))
(define (unbox fb) (box-v fb))

(define (fector? x) (box? x))


;; An [Fector X] is a (fox [Data X])
;; A [Data X] is one of:
;; - [Vector X]
;; - (list Nat X [Fector X])

(define fector/c
  (struct/c box 
            (or/c vector?
                  (list/c exact-nonnegative-integer?
                          any/c
                          (recursive-contract fector/c #:chaperone)))))

(define (make-fector n x)
  (box (make-vector n x)))

(define (fector . xs)
  (box (apply vector xs)))
  
(define (fector-length fv)
  (atomic 
   (λ ()
     (reroot! fv)
     (vector-length (unbox fv)))))
   
(define (build-fector n f)
  (box (build-vector n f)))

(define (fector-ref fv i)
  (atomic
   (λ ()
     (let ((v (unbox fv)))
       (cond 
         [(pair? v)
          (reroot! fv)
          (vector-ref (unbox fv) i)]
         [else
          (vector-ref v i)])))))
   
(define (fector-set fv i x)
  (atomic 
   (λ ()
     (reroot! fv)
     (let ((v (unbox fv)))
       (let ((old (vector-ref v i)))
         (vector-set! v i x)
         (let ((res (box v)))
           (set-box! fv (list i old res))
           res))))))

(define (reroot! fv)
  (match (unbox fv)
    [(list i x fv*)
     (reroot! fv*)     
     (let ((v (unbox fv*)))
       (let ((x* (vector-ref v i)))     
         (vector-set! v i x)
         (set-box! fv v)
         (set-box! fv* (list i x* fv))))]
    [_ (void)]))

(provide
 (contract-out
  [fector? (any/c . -> . boolean?)]
  [make-fector (exact-nonnegative-integer? any/c . -> . fector/c)]
  [fector (() #:rest list? . ->* . fector?)]
  [fector-length
   (fector/c . -> . exact-nonnegative-integer?)]
  [build-fector
   (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . any/c) . -> . fector?)]
  [fector-ref
   (fector/c exact-nonnegative-integer? . -> . any/c)]
  [fector-set
   (fector/c exact-nonnegative-integer? any/c . -> . any/c)]))
