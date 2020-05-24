#lang racket
; File: "nucleic2.scm"
;
; Author: Marc Feeley (feeley@iro.umontreal.ca)
; Last modification by Feeley: June 6, 1994.
; Modified for R5RS Scheme by William D Clinger: 22 October 1996.
; Last modification by Clinger: 19 March 1999.
;
; This program is a modified version of the program described in
;
;   M. Feeley, M. Turcotte, G. Lapalme.  Using Multilisp for Solving
;   Constraint Satisfaction Problems: an Application to Nucleic Acid 3D
;   Structure Determination.  Lisp and Symbolic Computation 7(2/3),
;   231-246, 1994.
;
; The differences between this program and the original are described in
;
;   P.H. Hartel, M. Feeley, et al.  Benchmarking Implementations of
;   Functional Languages with "Pseudoknot", a Float-Intensive Benchmark.
;   Journal of Functional Programming 6(4), 621-655, 1996.

; This procedure uses Marc Feeley's run-benchmark procedure to time
; the benchmark.

; PORTABILITY.
;
; This program should run in any R5RS-conforming implementation of Scheme.
; To run this program in an implementation that does not support the R5RS
; macro system, however, you will have to place a single quotation mark (')
; on the following line and also modify the "SYSTEM DEPENDENT CODE" below.

; ********** R5RS Scheme

(begin

(define-syntax FLOAT+    (syntax-rules () ((FLOAT+ x ...) (+ x ...))))
(define-syntax FLOAT-    (syntax-rules () ((FLOAT- x ...) (- x ...))))
(define-syntax FLOAT*    (syntax-rules () ((FLOAT* x ...) (* x ...))))
(define-syntax FLOAT/    (syntax-rules () ((FLOAT/ x ...) (/ x ...))))
(define-syntax FLOAT=    (syntax-rules () ((FLOAT=  x y)  (=  x y))))
(define-syntax FLOAT<    (syntax-rules () ((FLOAT<  x y)  (<  x y))))
(define-syntax FLOAT<=   (syntax-rules () ((FLOAT<= x y)  (<= x y))))
(define-syntax FLOAT>    (syntax-rules () ((FLOAT>  x y)  (>  x y))))
(define-syntax FLOAT>=   (syntax-rules () ((FLOAT>= x y)  (>= x y))))
(define-syntax FLOATsin  (syntax-rules () ((FLOATsin  x)  (sin  x))))
(define-syntax FLOATcos  (syntax-rules () ((FLOATcos  x)  (cos  x))))
(define-syntax FLOATatan (syntax-rules () ((FLOATatan x)  (atan x))))
(define-syntax FLOATsqrt (syntax-rules () ((FLOATsqrt x)  (sqrt x))))

(define-syntax FUTURE    (syntax-rules () ((FUTURE x) x)))
(define-syntax TOUCH     (syntax-rules () ((TOUCH x)  x)))

(define-syntax define-structure
  (syntax-rules ()
    ((define-structure #f
       name make make-constant (select1 ...) (set1 ...))
     (begin (define-syntax make
              (syntax-rules ()
                ((make select1 ...)
                 (vector select1 ...))))
            (define-syntax make-constant
              (syntax-rules ()
                ; The vectors that are passed to make-constant aren't quoted.
                ((make-constant . args)
                 (constant-maker make . args))))
            (define-selectors (select1 ...)
                              (0 1 2 3 4 5 6 7 8 9
                               10 11 12 13 14 15 16 17 18 19
                               20 21 22 23 24 25 26 27 28 29
                               30 31 32 33 34 35 36 37 38 39
                               40 41 42 43 44 45 46 47 48 49))
            (define-setters   (set1 ...)
                              (0 1 2 3 4 5 6 7 8 9
                               10 11 12 13 14 15 16 17 18 19
                               20 21 22 23 24 25 26 27 28 29
                               30 31 32 33 34 35 36 37 38 39
                               40 41 42 43 44 45 46 47 48 49))))
    ((define-structure pred?
       name make make-constant (select1 ...) (set1 ...))
     (begin (define-syntax pred?
              (syntax-rules ()
                ((pred? v)
                 (and (vector? v) (eq? (vector-ref v 0) 'name)))))
            (define-syntax make
              (syntax-rules ()
                ((make select1 ...)
                 (vector 'name select1 ...))))
            (define-syntax make-constant
              (syntax-rules ()
                ; The vectors that are passed to make-constant aren't quoted.
                ((make-constant . args)
                 (constant-maker make . args))))
            (define-selectors (select1 ...)
                              (1 2 3 4 5 6 7 8 9
                               10 11 12 13 14 15 16 17 18 19
                               20 21 22 23 24 25 26 27 28 29
                               30 31 32 33 34 35 36 37 38 39
                               40 41 42 43 44 45 46 47 48 49))
            (define-setters   (set1 ...)
                              (1 2 3 4 5 6 7 8 9
                               10 11 12 13 14 15 16 17 18 19
                               20 21 22 23 24 25 26 27 28 29
                               30 31 32 33 34 35 36 37 38 39
                               40 41 42 43 44 45 46 47 48 49))))))
(define-syntax constant-maker
  (syntax-rules ()
    ; The quotation marks are added here.
    ((constant-maker make arg ...)
     (make 'arg ...))))
(define-syntax define-selectors
  (syntax-rules ()
    ((define-selectors (select) (i i1 ...))
     (define-syntax select
       (syntax-rules ()
         ((select v) (vector-ref v i)))))
    ((define-selectors (select select1 ...) (i i1 ...))
     (begin (define-syntax select
              (syntax-rules ()
                ((select v) (vector-ref v i))))
            (define-selectors (select1 ...) (i1 ...))))))
(define-syntax define-setters
  (syntax-rules ()
    ((define-setters (set) (i i1 ...))
     (define-syntax set
       (syntax-rules ()
         ((set v x) (vector-set! v i x)))))
    ((define-setters (set set1 ...) (i i1 ...))
     (begin (define-syntax set
              (syntax-rules ()
                ((set v x) (vector-set! v i x))))
            (define-setters (set1 ...) (i1 ...))))))

(define ? any/c)

(define pt/c (vector/c flonum? flonum? flonum?))
(define-structure #f pt
  make-pt make-constant-pt
  (pt-x pt-y pt-z)
  (pt-x-set! pt-y-set! pt-z-set!))

(define tfo/c (vector/c flonum? flonum? flonum? flonum? flonum? flonum? flonum? flonum? flonum? flonum? flonum? flonum?))
(define-structure #f tfo
  make-tfo make-constant-tfo
  (tfo-a tfo-b tfo-c tfo-d tfo-e tfo-f tfo-g tfo-h tfo-i tfo-tx tfo-ty tfo-tz)
  (tfo-a-set! tfo-b-set! tfo-c-set! tfo-d-set! tfo-e-set! tfo-f-set!
   tfo-g-set! tfo-h-set! tfo-i-set! tfo-tx-set! tfo-ty-set! tfo-tz-set!))

(define-structure nuc? nuc
  make-nuc make-constant-nuc
  (nuc-dgf-base-tfo  ; defines the standard position for wc and wc-dumas
   nuc-P-O3*-275-tfo ; defines the standard position for the connect function
   nuc-P-O3*-180-tfo
   nuc-P-O3*-60-tfo
   nuc-P nuc-O1P nuc-O2P nuc-O5* nuc-C5*
   nuc-H5* nuc-H5**
   nuc-C4* nuc-H4* nuc-O4* nuc-C1* nuc-H1*
   nuc-C2* nuc-H2**
   nuc-O2* nuc-H2* nuc-C3* nuc-H3* nuc-O3*
   nuc-N1 nuc-N3 nuc-C2 nuc-C4 nuc-C5 nuc-C6)
  (nuc-dgf-base-tfo-set!
   nuc-P-O3*-275-tfo-set!
   nuc-P-O3*-180-tfo-set!
   nuc-P-O3*-60-tfo-set!
   nuc-P-set! nuc-O1P-set! nuc-O2P-set! nuc-O5*-set! nuc-C5*-set!
   nuc-H5*-set! nuc-H5**-set!
   nuc-C4*-set! nuc-H4*-set! nuc-O4*-set! nuc-C1*-set! nuc-H1*-set!
   nuc-C2*-set! nuc-H2**-set!
   nuc-O2*-set! nuc-H2*-set! nuc-C3*-set! nuc-H3*-set! nuc-O3*-set!
   nuc-N1-set! nuc-N3-set! nuc-C2-set! nuc-C4-set! nuc-C5-set! nuc-C6-set!))
(define nuc/c
  (vector/c tfo/c tfo/c tfo/c tfo/c
            pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c))

(define-structure rA? rA
  make-rA make-constant-rA
  (rA-dgf-base-tfo  ; defines the standard position for wc and wc-dumas
   rA-P-O3*-275-tfo ; defines the standard position for the connect function
   rA-P-O3*-180-tfo
   rA-P-O3*-60-tfo
   rA-P rA-O1P rA-O2P rA-O5* rA-C5*
   rA-H5* rA-H5**
   rA-C4* rA-H4* rA-O4* rA-C1* rA-H1*
   rA-C2* rA-H2**
   rA-O2* rA-H2* rA-C3* rA-H3* rA-O3*
   rA-N1 rA-N3 rA-C2 rA-C4 rA-C5 rA-C6
   rA-N6 rA-N7 rA-N9 rA-C8
   rA-H2 rA-H61 rA-H62 rA-H8)
  (rA-dgf-base-tfo-set!
   rA-P-O3*-275-tfo-set!
   rA-P-O3*-180-tfo-set!
   rA-P-O3*-60-tfo-set!
   rA-P-set! rA-O1P-set! rA-O2P-set! rA-O5*-set! rA-C5*-set!
   rA-H5*-set! rA-H5**-set!
   rA-C4*-set! rA-H4*-set! rA-O4*-set! rA-C1*-set! rA-H1*-set!
   rA-C2*-set! rA-H2**-set!
   rA-O2*-set! rA-H2*-set! rA-C3*-set! rA-H3*-set! rA-O3*-set!
   rA-N1-set! rA-N3-set! rA-C2-set! rA-C4-set! rA-C5-set! rA-C6-set!
   rA-N6-set! rA-N7-set! rA-N9-set! rA-C8-set!
   rA-H2-set! rA-H61-set! rA-H62-set! rA-H8-set!))
(define rA/c
  (vector/c (one-of/c 'rA)
            tfo/c tfo/c tfo/c tfo/c
            pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c  pt/c))

(define-structure rC? rC
  make-rC make-constant-rC
  (rC-dgf-base-tfo  ; defines the standard position for wc and wc-dumas
   rC-P-O3*-275-tfo ; defines the standard position for the connect function
   rC-P-O3*-180-tfo
   rC-P-O3*-60-tfo
   rC-P rC-O1P rC-O2P rC-O5* rC-C5*
   rC-H5* rC-H5**
   rC-C4* rC-H4* rC-O4* rC-C1* rC-H1*
   rC-C2* rC-H2**
   rC-O2* rC-H2* rC-C3* rC-H3* rC-O3*
   rC-N1 rC-N3 rC-C2 rC-C4 rC-C5 rC-C6
   rC-N4 rC-O2 rC-H41 rC-H42 rC-H5 rC-H6)
  (rC-dgf-base-tfo-set!
   rC-P-O3*-275-tfo-set!
   rC-P-O3*-180-tfo-set!
   rC-P-O3*-60-tfo-set!
   rC-P-set! rC-O1P-set! rC-O2P-set! rC-O5*-set! rC-C5*-set!
   rC-H5*-set! rC-H5**-set!
   rC-C4*-set! rC-H4*-set! rC-O4*-set! rC-C1*-set! rC-H1*-set!
   rC-C2*-set! rC-H2**-set!
   rC-O2*-set! rC-H2*-set! rC-C3*-set! rC-H3*-set! rC-O3*-set!
   rC-N1-set! rC-N3-set! rC-C2-set! rC-C4-set! rC-C5-set! rC-C6-set!
   rC-N4-set! rC-O2-set! rC-H41-set! rC-H42-set! rC-H5-set! rC-H6-set!))
(define rC/c
  (vector/c (one-of/c 'rC)
            tfo/c tfo/c tfo/c tfo/c
            pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c))

(define-structure rG? rG
  make-rG make-constant-rG
  (rG-dgf-base-tfo  ; defines the standard position for wc and wc-dumas
   rG-P-O3*-275-tfo ; defines the standard position for the connect function
   rG-P-O3*-180-tfo
   rG-P-O3*-60-tfo
   rG-P rG-O1P rG-O2P rG-O5* rG-C5*
   rG-H5* rG-H5**
   rG-C4* rG-H4* rG-O4* rG-C1* rG-H1*
   rG-C2* rG-H2**
   rG-O2* rG-H2* rG-C3* rG-H3* rG-O3*
   rG-N1 rG-N3 rG-C2 rG-C4 rG-C5 rG-C6
   rG-N2 rG-N7 rG-N9 rG-C8 rG-O6
   rG-H1 rG-H21 rG-H22 rG-H8)
  (rG-dgf-base-tfo-set!
   rG-P-O3*-275-tfo-set!
   rG-P-O3*-180-tfo-set!
   rG-P-O3*-60-tfo-set!
   rG-P-set! rG-O1P-set! rG-O2P-set! rG-O5*-set! rG-C5*-set!
   rG-H5*-set! rG-H5**-set!
   rG-C4*-set! rG-H4*-set! rG-O4*-set! rG-C1*-set! rG-H1*-set!
   rG-C2*-set! rG-H2**-set!
   rG-O2*-set! rG-H2*-set! rG-C3*-set! rG-H3*-set! rG-O3*-set!
   rG-N1-set! rG-N3-set! rG-C2-set! rG-C4-set! rG-C5-set! rG-C6-set!
   rG-N2-set! rG-N7-set! rG-N9-set! rG-C8-set! rG-O6-set!
   rG-H1-set! rG-H21-set! rG-H22-set! rG-H8-set!))
(define rG/c
  (vector/c (one-of/c 'rG)
            tfo/c tfo/c tfo/c tfo/c
            pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c))

(define-structure rU? rU
  make-rU make-constant-rU
  (rU-dgf-base-tfo  ; defines the standard position for wc and wc-dumas
   rU-P-O3*-275-tfo ; defines the standard position for the connect function
   rU-P-O3*-180-tfo
   rU-P-O3*-60-tfo
   rU-P rU-O1P rU-O2P rU-O5* rU-C5*
   rU-H5* rU-H5**
   rU-C4* rU-H4* rU-O4* rU-C1* rU-H1*
   rU-C2* rU-H2**
   rU-O2* rU-H2* rU-C3* rU-H3* rU-O3*
   rU-N1 rU-N3 rU-C2 rU-C4 rU-C5 rU-C6
   rU-O2 rU-O4 rU-H3 rU-H5 rU-H6)
  (rU-dgf-base-tfo-set!
   rU-P-O3*-275-tfo-set!
   rU-P-O3*-180-tfo-set!
   rU-P-O3*-60-tfo-set!
   rU-P-set! rU-O1P-set! rU-O2P-set! rU-O5*-set! rU-C5*-set!
   rU-H5*-set! rU-H5**-set!
   rU-C4*-set! rU-H4*-set! rU-O4*-set! rU-C1*-set! rU-H1*-set!
   rU-C2*-set! rU-H2**-set!
   rU-O2*-set! rU-H2*-set! rU-C3*-set! rU-H3*-set! rU-O3*-set!
   rU-N1-set! rU-N3-set! rU-C2-set! rU-C4-set! rU-C5-set! rU-C6-set!
   rU-O2-set! rU-O4-set! rU-H3-set! rU-H5-set! rU-H6-set!))
(define rU/c
  (vector/c (one-of/c 'rU)
            tfo/c tfo/c tfo/c tfo/c
            pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c pt/c))

(define-structure #f var
  make-var make-constant-var
  (var-id var-tfo var-nuc)
  (var-id-set! var-tfo-set! var-nuc-set!))
(define var/c (vector/c integer? tfo/c nuc/c))

; Comment out the next three syntax definitions if you want
; lazy computation.

(define-syntax mk-var
  (syntax-rules ()
    ((mk-var i tfo nuc)
     (make-var i tfo nuc))))

(define-syntax absolute-pos
  (syntax-rules ()
    ((absolute-pos var p)
     (tfo-apply (var-tfo var) p))))

(define-syntax lazy-computation-of
  (syntax-rules ()
    ((lazy-computation-of expr)
     expr)))

; Uncomment the next three syntax definitions if you want
; lazy computation.

; (define-syntax mk-var
;   (syntax-rules ()
;     ((mk-var i tfo nuc)
;      (make-var i tfo (make-relative-nuc tfo nuc)))))
;
; (define-syntax absolute-pos
;   (syntax-rules ()
;     ((absolute-pos var p)
;      (force p))))
;
; (define-syntax lazy-computation-of
;   (syntax-rules ()
;     ((lazy-computation-of expr)
;      (delay expr))))

(define-syntax atom-pos
  (syntax-rules ()
    ((atom-pos atom var)
     (let ((v var))
       (absolute-pos v (atom (var-nuc v)))))))

)

; -- MATH UTILITIES -----------------------------------------------------------

(define constant-pi          3.14159265358979323846)
(define constant-minus-pi   -3.14159265358979323846)
(define constant-pi/2        1.57079632679489661923)
(define constant-minus-pi/2 -1.57079632679489661923)

(define (math-atan2 y x)
  (cond ((FLOAT> x 0.0)
         (FLOATatan (FLOAT/ y x)))
        ((FLOAT< y 0.0)
         (if (FLOAT= x 0.0)
           constant-minus-pi/2
           (FLOAT+ (FLOATatan (FLOAT/ y x)) constant-minus-pi)))
        (else
         (if (FLOAT= x 0.0)
           constant-pi/2
           (FLOAT+ (FLOATatan (FLOAT/ y x)) constant-pi)))))

; -- POINTS -------------------------------------------------------------------

(define (pt-sub p1 p2)
  (make-pt (FLOAT- (pt-x p1) (pt-x p2))
           (FLOAT- (pt-y p1) (pt-y p2))
           (FLOAT- (pt-z p1) (pt-z p2))))

(define (pt-dist p1 p2)
  (let ((dx (FLOAT- (pt-x p1) (pt-x p2)))
        (dy (FLOAT- (pt-y p1) (pt-y p2)))
        (dz (FLOAT- (pt-z p1) (pt-z p2))))
    (FLOATsqrt (FLOAT+ (FLOAT* dx dx) (FLOAT* dy dy) (FLOAT* dz dz)))))

(define (pt-phi p)
  (let* ((x (pt-x p))
         (y (pt-y p))
         (z (pt-z p))
         (b (math-atan2 x z)))
    (math-atan2 (FLOAT+ (FLOAT* (FLOATcos b) z) (FLOAT* (FLOATsin b) x)) y)))

(define (pt-theta p)
  (math-atan2 (pt-x p) (pt-z p)))

; -- COORDINATE TRANSFORMATIONS -----------------------------------------------

; The notation for the transformations follows "Paul, R.P. (1981) Robot
; Manipulators.  MIT Press." with the exception that our transformation
; matrices don't have the perspective terms and are the transpose of
; Paul's one.  See also "M\"antyl\"a, M. (1985) An Introduction to
; Solid Modeling, Computer Science Press" Appendix A.
;
; The components of a transformation matrix are named like this:
;
;  a  b  c
;  d  e  f
;  g  h  i
; tx ty tz
;
; The components tx, ty, and tz are the translation vector.

(define tfo-id  ; the identity transformation matrix
  '#(1.0 0.0 0.0
     0.0 1.0 0.0
     0.0 0.0 1.0
     0.0 0.0 0.0))

; The function "tfo-apply" multiplies a transformation matrix, tfo, by a
; point vector, p.  The result is a new point.

(define (tfo-apply tfo p)
  (let ((x (pt-x p))
        (y (pt-y p))
        (z (pt-z p)))
    (make-pt
     (FLOAT+ (FLOAT* x (tfo-a tfo)) 
             (FLOAT* y (tfo-d tfo)) 
             (FLOAT* z (tfo-g tfo)) 
             (tfo-tx tfo))
     (FLOAT+ (FLOAT* x (tfo-b tfo)) 
             (FLOAT* y (tfo-e tfo))
             (FLOAT* z (tfo-h tfo))
             (tfo-ty tfo))
     (FLOAT+ (FLOAT* x (tfo-c tfo)) 
             (FLOAT* y (tfo-f tfo))
             (FLOAT* z (tfo-i tfo))
             (tfo-tz tfo)))))

; The function "tfo-combine" multiplies two transformation matrices A and B.
; The result is a new matrix which cumulates the transformations described
; by A and B.

(define (tfo-combine A B)
  (make-tfo
   (FLOAT+ (FLOAT* (tfo-a A) (tfo-a B))
           (FLOAT* (tfo-b A) (tfo-d B))
           (FLOAT* (tfo-c A) (tfo-g B)))
   (FLOAT+ (FLOAT* (tfo-a A) (tfo-b B))
           (FLOAT* (tfo-b A) (tfo-e B))
           (FLOAT* (tfo-c A) (tfo-h B)))
   (FLOAT+ (FLOAT* (tfo-a A) (tfo-c B))
           (FLOAT* (tfo-b A) (tfo-f B))
           (FLOAT* (tfo-c A) (tfo-i B)))
   (FLOAT+ (FLOAT* (tfo-d A) (tfo-a B))
           (FLOAT* (tfo-e A) (tfo-d B))
           (FLOAT* (tfo-f A) (tfo-g B)))
   (FLOAT+ (FLOAT* (tfo-d A) (tfo-b B))
           (FLOAT* (tfo-e A) (tfo-e B))
           (FLOAT* (tfo-f A) (tfo-h B)))
   (FLOAT+ (FLOAT* (tfo-d A) (tfo-c B))
           (FLOAT* (tfo-e A) (tfo-f B))
           (FLOAT* (tfo-f A) (tfo-i B)))
   (FLOAT+ (FLOAT* (tfo-g A) (tfo-a B))
           (FLOAT* (tfo-h A) (tfo-d B))
           (FLOAT* (tfo-i A) (tfo-g B)))
   (FLOAT+ (FLOAT* (tfo-g A) (tfo-b B))
           (FLOAT* (tfo-h A) (tfo-e B))
           (FLOAT* (tfo-i A) (tfo-h B)))
   (FLOAT+ (FLOAT* (tfo-g A) (tfo-c B))
           (FLOAT* (tfo-h A) (tfo-f B))
           (FLOAT* (tfo-i A) (tfo-i B)))
   (FLOAT+ (FLOAT* (tfo-tx A) (tfo-a B))
           (FLOAT* (tfo-ty A) (tfo-d B))
           (FLOAT* (tfo-tz A) (tfo-g B))
           (tfo-tx B))
   (FLOAT+ (FLOAT* (tfo-tx A) (tfo-b B))
           (FLOAT* (tfo-ty A) (tfo-e B))
           (FLOAT* (tfo-tz A) (tfo-h B))
           (tfo-ty B))
   (FLOAT+ (FLOAT* (tfo-tx A) (tfo-c B))
           (FLOAT* (tfo-ty A) (tfo-f B))
           (FLOAT* (tfo-tz A) (tfo-i B))
           (tfo-tz B))))

; The function "tfo-inv-ortho" computes the inverse of a homogeneous
; transformation matrix.

(define (tfo-inv-ortho tfo)
  (let* ((tx (tfo-tx tfo))
         (ty (tfo-ty tfo))
         (tz (tfo-tz tfo)))
    (make-tfo
     (tfo-a tfo) (tfo-d tfo) (tfo-g tfo)
     (tfo-b tfo) (tfo-e tfo) (tfo-h tfo)
     (tfo-c tfo) (tfo-f tfo) (tfo-i tfo)
     (FLOAT- (FLOAT+ (FLOAT* (tfo-a tfo) tx)
                     (FLOAT* (tfo-b tfo) ty)
                     (FLOAT* (tfo-c tfo) tz)))
     (FLOAT- (FLOAT+ (FLOAT* (tfo-d tfo) tx)
                     (FLOAT* (tfo-e tfo) ty)
                     (FLOAT* (tfo-f tfo) tz)))
     (FLOAT- (FLOAT+ (FLOAT* (tfo-g tfo) tx)
                     (FLOAT* (tfo-h tfo) ty)
                     (FLOAT* (tfo-i tfo) tz))))))

; Given three points p1, p2, and p3, the function "tfo-align" computes
; a transformation matrix such that point p1 gets mapped to (0,0,0), p2 gets
; mapped to the Y axis and p3 gets mapped to the YZ plane.

(define (tfo-align p1 p2 p3)
  (let* ((x1 (pt-x p1))       (y1 (pt-y p1))       (z1 (pt-z p1))
         (x3 (pt-x p3))       (y3 (pt-y p3))       (z3 (pt-z p3))
         (x31 (FLOAT- x3 x1)) (y31 (FLOAT- y3 y1)) (z31 (FLOAT- z3 z1))
         (rotpY (pt-sub p2 p1))
         (Phi (pt-phi rotpY))
         (Theta (pt-theta rotpY))
         (sinP (FLOATsin Phi))
         (sinT (FLOATsin Theta))
         (cosP (FLOATcos Phi))
         (cosT (FLOATcos Theta))
         (sinPsinT (FLOAT* sinP sinT))
         (sinPcosT (FLOAT* sinP cosT))
         (cosPsinT (FLOAT* cosP sinT))
         (cosPcosT (FLOAT* cosP cosT))
         (rotpZ 
          (make-pt 
           (FLOAT- (FLOAT* cosT x31)
                   (FLOAT* sinT z31))
           (FLOAT+ (FLOAT* sinPsinT x31)
                   (FLOAT* cosP y31)
                   (FLOAT* sinPcosT z31))
           (FLOAT+ (FLOAT* cosPsinT x31)
                   (FLOAT- (FLOAT* sinP y31))
                   (FLOAT* cosPcosT z31))))
         (Rho (pt-theta rotpZ))
         (cosR (FLOATcos Rho))
         (sinR (FLOATsin Rho))
         (x (FLOAT+ (FLOAT- (FLOAT* x1 cosT))
                    (FLOAT* z1 sinT)))
         (y (FLOAT- (FLOAT- (FLOAT- (FLOAT* x1 sinPsinT))
                            (FLOAT* y1 cosP))
                    (FLOAT* z1 sinPcosT)))
         (z (FLOAT- (FLOAT+ (FLOAT- (FLOAT* x1 cosPsinT))
                            (FLOAT* y1 sinP))
                    (FLOAT* z1 cosPcosT))))
    (make-tfo
     (FLOAT- (FLOAT* cosT cosR) (FLOAT* cosPsinT sinR))
     sinPsinT
     (FLOAT+ (FLOAT* cosT sinR) (FLOAT* cosPsinT cosR))
     (FLOAT* sinP sinR)
     cosP
     (FLOAT- (FLOAT* sinP cosR))
     (FLOAT- (FLOAT- (FLOAT* sinT cosR)) (FLOAT* cosPcosT sinR))
     sinPcosT
     (FLOAT+ (FLOAT- (FLOAT* sinT sinR)) (FLOAT* cosPcosT cosR))
     (FLOAT- (FLOAT* x cosR) (FLOAT* z sinR))
     y
     (FLOAT+ (FLOAT* x sinR) (FLOAT* z cosR)))))

; -- NUCLEIC ACID CONFORMATIONS DATA BASE -------------------------------------

; Numbering of atoms follows the paper:
;
; IUPAC-IUB Joint Commission on Biochemical Nomenclature (JCBN)
; (1983) Abbreviations and Symbols for the Description of
; Conformations of Polynucleotide Chains.  Eur. J. Biochem 131,
; 9-15.
;
; In the atom names, we have used "*" instead of "'".

; Define part common to all 4 nucleotide types.

; Define remaining atoms for each nucleotide type.

; Database of nucleotide conformations:

; -- PARTIAL INSTANTIATIONS ---------------------------------------------------

(define (get-var id lst)
  (cond [(null? lst) (error 'get-var "not found ~a" id)]
        [else
         (let ((v (car lst)))
           (if (= id (var-id v))
               v
               (get-var id (cdr lst))))]))

(define (make-relative-nuc tfo n)
  (cond ((rA? n)
         (make-rA
           (nuc-dgf-base-tfo  n)
           (nuc-P-O3*-275-tfo n)
           (nuc-P-O3*-180-tfo n)
           (nuc-P-O3*-60-tfo  n)
           (lazy-computation-of (tfo-apply tfo (nuc-P    n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O1P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N1   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N3   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C6   n)))
           (lazy-computation-of (tfo-apply tfo (rA-N6    n)))
           (lazy-computation-of (tfo-apply tfo (rA-N7    n)))
           (lazy-computation-of (tfo-apply tfo (rA-N9    n)))
           (lazy-computation-of (tfo-apply tfo (rA-C8    n)))
           (lazy-computation-of (tfo-apply tfo (rA-H2    n)))
           (lazy-computation-of (tfo-apply tfo (rA-H61   n)))
           (lazy-computation-of (tfo-apply tfo (rA-H62   n)))
           (lazy-computation-of (tfo-apply tfo (rA-H8    n)))))
        ((rC? n)
         (make-rC
           (nuc-dgf-base-tfo  n)
           (nuc-P-O3*-275-tfo n)
           (nuc-P-O3*-180-tfo n)
           (nuc-P-O3*-60-tfo  n)
           (lazy-computation-of (tfo-apply tfo (nuc-P    n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O1P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N1   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N3   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C6   n)))
           (lazy-computation-of (tfo-apply tfo (rC-N4    n)))
           (lazy-computation-of (tfo-apply tfo (rC-O2    n)))
           (lazy-computation-of (tfo-apply tfo (rC-H41   n)))
           (lazy-computation-of (tfo-apply tfo (rC-H42   n)))
           (lazy-computation-of (tfo-apply tfo (rC-H5    n)))
           (lazy-computation-of (tfo-apply tfo (rC-H6    n)))))
        ((rG? n)
         (make-rG
           (nuc-dgf-base-tfo  n)
           (nuc-P-O3*-275-tfo n)
           (nuc-P-O3*-180-tfo n)
           (nuc-P-O3*-60-tfo  n)
           (lazy-computation-of (tfo-apply tfo (nuc-P    n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O1P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N1   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N3   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C6   n)))
           (lazy-computation-of (tfo-apply tfo (rG-N2    n)))
           (lazy-computation-of (tfo-apply tfo (rG-N7    n)))
           (lazy-computation-of (tfo-apply tfo (rG-N9    n)))
           (lazy-computation-of (tfo-apply tfo (rG-C8    n)))
           (lazy-computation-of (tfo-apply tfo (rG-O6    n)))
           (lazy-computation-of (tfo-apply tfo (rG-H1    n)))
           (lazy-computation-of (tfo-apply tfo (rG-H21   n)))
           (lazy-computation-of (tfo-apply tfo (rG-H22   n)))
           (lazy-computation-of (tfo-apply tfo (rG-H8    n)))))
        (else
         (make-rU
           (nuc-dgf-base-tfo  n)
           (nuc-P-O3*-275-tfo n)
           (nuc-P-O3*-180-tfo n)
           (nuc-P-O3*-60-tfo  n)
           (lazy-computation-of (tfo-apply tfo (nuc-P    n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O1P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2P  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H5** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O4*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H1*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2** n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H2*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-H3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-O3*  n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N1   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-N3   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C2   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C4   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C5   n)))
           (lazy-computation-of (tfo-apply tfo (nuc-C6   n)))
           (lazy-computation-of (tfo-apply tfo (rU-O2    n)))
           (lazy-computation-of (tfo-apply tfo (rU-O4    n)))
           (lazy-computation-of (tfo-apply tfo (rU-H3    n)))
           (lazy-computation-of (tfo-apply tfo (rU-H5    n)))
           (lazy-computation-of (tfo-apply tfo (rU-H6    n)))))))

; -- SEARCH -------------------------------------------------------------------

; Sequential backtracking algorithm

(define (search partial-inst domains constraint?)
  (if (null? domains)
    (list partial-inst)
    (let ((remaining-domains (cdr domains)))

      (define (try-assignments lst)
        (if (null? lst)
          '()
          (let ((var (car lst)))
            (if (constraint? var partial-inst)
              (let* ((subsols1
                       (search
                         (cons var partial-inst)
                         remaining-domains
                         constraint?))
                     (subsols2
                       (try-assignments (cdr lst))))
                (append subsols1 subsols2))
              (try-assignments (cdr lst))))))

      (try-assignments ((car domains) partial-inst)))))

; -- DOMAINS ------------------------------------------------------------------

; Primary structure:   strand A CUGCCACGUCUG, strand B CAGACGUGGCAG
;
; Secondary structure: strand A CUGCCACGUCUG
;                               ||||||||||||
;                               GACGGUGCAGAC strand B
;
; Tertiary structure:
;
;    5' end of strand A C1----G12 3' end of strand B
;                     U2-------A11
;                    G3-------C10
;                    C4-----G9
;                     C5---G8
;                        A6
;                      G6-C7
;                     C5----G8
;                    A4-------U9
;                    G3--------C10
;                     A2-------U11
;   5' end of strand B C1----G12 3' end of strand A
;
; "helix", "stacked" and "connected" describe the spatial relationship
; between two consecutive nucleotides. E.g. the nucleotides C1 and U2
; from the strand A.
;
; "wc" (stands for Watson-Crick and is a type of base-pairing),
; and "wc-dumas" describe the spatial relationship between 
; nucleotides from two chains that are growing in opposite directions.
; E.g. the nucleotides C1 from strand A and G12 from strand B.

; Dynamic Domains

; Given,
;   "ref" a nucleotide which is already positioned,
;   "nuc" the nucleotide to be placed,
;   and "tfo" a transformation matrix which expresses the desired
;   relationship between "ref" and "nuc",
; the function "dgf-base" computes the transformation matrix that
; places the nucleotide "nuc" in the given relationship to "ref".

(define (dgf-base tfo ref nuc)
  (let* ((ref-nuc (var-nuc ref))
         (align
          (tfo-inv-ortho
            (cond ((rA? ref-nuc)
                   (tfo-align (atom-pos nuc-C1* ref)
                              (atom-pos rA-N9   ref)
                              (atom-pos nuc-C4  ref)))
                  ((rC? ref-nuc)
                   (tfo-align (atom-pos nuc-C1* ref)
                              (atom-pos nuc-N1  ref)
                              (atom-pos nuc-C2  ref)))
                  ((rG? ref-nuc)
                   (tfo-align (atom-pos nuc-C1* ref)
                              (atom-pos rG-N9   ref)
                              (atom-pos nuc-C4  ref)))
                  (else
                   (tfo-align (atom-pos nuc-C1* ref)
                              (atom-pos nuc-N1  ref)
                              (atom-pos nuc-C2  ref)))))))
    (tfo-combine (nuc-dgf-base-tfo nuc)
                 (tfo-combine tfo align))))

; Placement of first nucleotide.

(define (reference nuc i)
  (lambda (partial-inst)
    (list (mk-var i tfo-id nuc))))

; The transformation matrix for wc is from:
;
; Chandrasekaran R. et al (1989) A Re-Examination of the Crystal
; Structure of A-DNA Using Fiber Diffraction Data. J. Biomol.
; Struct. & Dynamics 6(6):1189-1202.

(define wc-tfo
  '#(-1.0000  0.0028 -0.0019
      0.0028  0.3468 -0.9379
     -0.0019 -0.9379 -0.3468
     -0.0080  6.0730  8.7208))

(define (wc nuc i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (tfo (dgf-base wc-tfo ref nuc)))
      (list (mk-var i tfo nuc)))))

(define wc-Dumas-tfo
  '#(-0.9737 -0.1834  0.1352
     -0.1779  0.2417 -0.9539
      0.1422 -0.9529 -0.2679
      0.4837  6.2649  8.0285))
         
(define (wc-Dumas nuc i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (tfo (dgf-base wc-Dumas-tfo ref nuc)))
      (list (mk-var i tfo nuc)))))

(define helix5*-tfo
  '#( 0.9886 -0.0961  0.1156
      0.1424  0.8452 -0.5152
     -0.0482  0.5258  0.8492
     -3.8737  0.5480  3.8024))

(define (helix5* nuc i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (tfo (dgf-base helix5*-tfo ref nuc)))
      (list (mk-var i tfo nuc)))))

(define helix3*-tfo
  '#( 0.9886  0.1424 -0.0482
     -0.0961  0.8452  0.5258
      0.1156 -0.5152  0.8492
      3.4426  2.0474 -3.7042))

(define (helix3* nuc i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (tfo (dgf-base helix3*-tfo ref nuc)))
      (list (mk-var i tfo nuc)))))

(define G37-A38-tfo
  '#( 0.9991  0.0164 -0.0387
     -0.0375  0.7616 -0.6470
      0.0189  0.6478  0.7615
     -3.3018  0.9975  2.5585))

(define (G37-A38 nuc i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (tfo (dgf-base G37-A38-tfo ref nuc)))
      (mk-var i tfo nuc))))

(define (stacked5* nuc i j)
  (lambda (partial-inst)
    (cons ((G37-A38 nuc i j) partial-inst)
          ((helix5* nuc i j) partial-inst))))

(define A38-G37-tfo
  '#( 0.9991 -0.0375  0.0189
      0.0164  0.7616  0.6478 
     -0.0387 -0.6470  0.7615
      3.3819  0.7718 -2.5321))

(define (A38-G37 nuc i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (tfo (dgf-base A38-G37-tfo ref nuc)))
      (mk-var i tfo nuc))))
   
(define (stacked3* nuc i j)
  (lambda (partial-inst)
    (cons ((A38-G37 nuc i j) partial-inst)
          ((helix3* nuc i j) partial-inst))))

(define (P-O3* nucs i j)
  (lambda (partial-inst)
    (let* ((ref (get-var j partial-inst))
           (align
             (tfo-inv-ortho
               (tfo-align (atom-pos nuc-O3* ref)
                          (atom-pos nuc-C3* ref)
                          (atom-pos nuc-C4* ref)))))
      (let loop ((lst nucs) (domains '()))
        (if (null? lst)
          domains
          (let ((nuc (car lst)))
            (let ((tfo-60 (tfo-combine (nuc-P-O3*-60-tfo nuc) align))
                  (tfo-180 (tfo-combine (nuc-P-O3*-180-tfo nuc) align))
                  (tfo-275 (tfo-combine (nuc-P-O3*-275-tfo nuc) align)))
              (loop (cdr lst)
                    (cons (mk-var i tfo-60 nuc)
                          (cons (mk-var i tfo-180 nuc)
                                (cons (mk-var i tfo-275 nuc) domains)))))))))))

; -- PROBLEM STATEMENT --------------------------------------------------------

; Define anticodon problem -- Science 253:1255 Figure 3a, 3b and 3c

; Anticodon constraint

(define (anticodon-constraint? v partial-inst)
  (if (= (var-id v) 33)
    (let ((p   (atom-pos nuc-P (get-var 34 partial-inst))) ; P in nucleotide 34
          (o3* (atom-pos nuc-O3* v)))                      ; O3' in nucl. 33
      (FLOAT<= (pt-dist p o3*) 3.0))                       ; check distance
    #t))

(define (anticodon rAs rA rC rCs rG rGs rU rUs)

  (define anticodon-domains
    (list 
     (reference rC  27   )
     (helix5*   rC  28 27)
     (helix5*   rA  29 28)
     (helix5*   rG  30 29)
     (helix5*   rA  31 30)
     (wc        rU  39 31)
     (helix5*   rC  40 39)
     (helix5*   rU  41 40)
     (helix5*   rG  42 41)
     (helix5*   rG  43 42)
     (stacked3* rA  38 39)
     (stacked3* rG  37 38)
     (stacked3* rA  36 37)
     (stacked3* rA  35 36)
     (stacked3* rG  34 35);<-. Distance
     (P-O3*     rCs 32 31);  | Constraint
     (P-O3*     rUs 33 32);<-' 3.0 Angstroms
     ))

  (search '() anticodon-domains anticodon-constraint?))

; Pseudoknot constraint

(define (pseudoknot-constraint? v partial-inst)
  (case (var-id v)
    ((18)
     (let ((p   (atom-pos nuc-P (get-var 19 partial-inst)))
           (o3* (atom-pos nuc-O3* v)))
       (FLOAT<= (pt-dist p o3*) 4.0)))
    ((6)
     (let ((p   (atom-pos nuc-P (get-var 7 partial-inst)))
           (o3* (atom-pos nuc-O3* v)))
       (FLOAT<= (pt-dist p o3*) 4.5)))
    (else
     #t)))

(define (pseudoknot rA rAs rC rCs rG rGs rU rUs rG* rU*)

  ; Define pseudoknot problem -- Science 253:1255 Figure 4a and 4b

  (define pseudoknot-domains
    (list
     (reference rA  23   )
     (wc-Dumas  rU   8 23)
     (helix3*   rG  22 23)
     (wc-Dumas  rC   9 22)
     (helix3*   rG  21 22)
     (wc-Dumas  rC  10 21)
     (helix3*   rC  20 21)
     (wc-Dumas  rG  11 20)
     (helix3*   rU* 19 20);<-.
     (wc-Dumas  rA  12 19);  | Distance
     ;                       ;  | Constraint
     ; Helix 1               ;  | 4.0 Angstroms
     (helix3*   rC   3 19);  |
     (wc-Dumas  rG  13  3);  |
     (helix3*   rC   2  3);  |
     (wc-Dumas  rG  14  2);  |
     (helix3*   rC   1  2);  |
     (wc-Dumas  rG* 15  1);  |
     ;                       ;  |
     ; L2 LOOP               ;  |
     (P-O3*     rUs 16 15);  |
     (P-O3*     rCs 17 16);  |
     (P-O3*     rAs 18 17);<-'
     ;
     ; L1 LOOP
     (helix3*   rU   7  8);<-.
     (P-O3*     rCs  4  3);  | Constraint
     (stacked5* rU   5  4);  | 4.5 Angstroms
     (stacked5* rC   6  5);<-'
     ))
  


  (search '() pseudoknot-domains pseudoknot-constraint?))

; -- TESTING -----------------------------------------------------------------

(define (list-of-atoms n)
  (append (list-of-common-atoms n)
          (list-of-specific-atoms n)))

(define (list-of-common-atoms n)
  (list
    (nuc-P    n)
    (nuc-O1P  n)
    (nuc-O2P  n)
    (nuc-O5*  n)
    (nuc-C5*  n)
    (nuc-H5*  n)
    (nuc-H5** n)
    (nuc-C4*  n)
    (nuc-H4*  n)
    (nuc-O4*  n)
    (nuc-C1*  n)
    (nuc-H1*  n)
    (nuc-C2*  n)
    (nuc-H2** n)
    (nuc-O2*  n)
    (nuc-H2*  n)
    (nuc-C3*  n)
    (nuc-H3*  n)
    (nuc-O3*  n)
    (nuc-N1   n)
    (nuc-N3   n)
    (nuc-C2   n)
    (nuc-C4   n)
    (nuc-C5   n)
    (nuc-C6   n)))

(define (list-of-specific-atoms n)
  (cond ((rA? n)
         (list
           (rA-N6   n)
           (rA-N7   n)
           (rA-N9   n)
           (rA-C8   n)
           (rA-H2   n)
           (rA-H61  n)
           (rA-H62  n)
           (rA-H8   n)))
        ((rC? n)
         (list
           (rC-N4   n)
           (rC-O2   n)
           (rC-H41  n)
           (rC-H42  n)
           (rC-H5   n)
           (rC-H6   n)))
        ((rG? n)
         (list
           (rG-N2   n)
           (rG-N7   n)
           (rG-N9   n)
           (rG-C8   n)
           (rG-O6   n)
           (rG-H1   n)
           (rG-H21  n)
           (rG-H22  n)
           (rG-H8   n)))
        (else
         (list
           (rU-O2   n)
           (rU-O4   n)
           (rU-H3   n)
           (rU-H5   n)
           (rU-H6   n)))))

(define (var-most-distant-atom v)

  (define (distance pos)
    (let ((abs-pos (absolute-pos v pos)))
      (let ((x (pt-x abs-pos)) (y (pt-y abs-pos)) (z (pt-z abs-pos)))
        (FLOATsqrt (FLOAT+ (FLOAT* x x) (FLOAT* y y) (FLOAT* z z))))))

  (maximum (map distance (list-of-atoms (var-nuc v)))))

(define (sol-most-distant-atom s)
  (maximum (map var-most-distant-atom s)))

(define (most-distant-atom sols)
  (maximum (map sol-most-distant-atom sols)))

(define (maximum lst)
  (cond
    [(null? lst) (error 'maximum "empty list")]
    [else
     (let loop ((m (car lst)) (l (cdr lst)))
       (if (null? l)
           m
           (let ((x (car l)))
             (loop (if (FLOAT> x m) x m) (cdr l)))))]))

(define (check rA rAs rC rCs rG rGs rU rUs rG* rU*)
  (length (pseudoknot rA rAs rC rCs rG rGs rU rUs rG* rU*)))

(define (run rA rAs rC rCs rG rGs rU rUs rG* rU*)
  (most-distant-atom (pseudoknot rA rAs rC rCs rG rGs rU rUs rG* rU*)))

; To run program, evaluate: (run)

;(time (let loop ((i 100)) (if (zero? i) 'done (begin (run) (loop (- i 1))))))
(provide
 (contract-out
  [run (-> rA/c (listof rA/c)
           rC/c (listof rC/c)
           rG/c (listof rG/c)
           rU/c (listof rU/c)
           rG/c
           rU/c
        any/c)]
  ))
