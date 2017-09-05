#lang typed/racket/base

(provide prims-04-02@)

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         racket/set
         racket/flonum
         racket/fixnum
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         math/base
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.2 Numbers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-02@
  (import prim-runtime^)
  (export)

  ;;;;; 4.2.1 Number Types
  (def-pred number?)
  (def-alias complex? number?)
  (def-pred real?)
  (def-pred rational?)
  (def-pred integer?)
  (def-pred exact-integer?)
  (def-pred exact-nonnegative-integer?)
  (def-pred exact-positive-integer?)
  (def-pred inexact-real?)
  (def-pred fixnum?)
  (def-pred flonum?)
  (def-pred double-flonum?)
  (def-pred single-flonum?)
  (def-pred zero? (number?))
  (def-pred positive? (real?))
  (def-pred negative? (real?))
  (def-pred even? (integer?))
  (def-pred odd? (integer?))
  (def-pred exact? (number?))
  (def-pred inexact? (number?))
  (def inexact->exact (number? . -> . exact?))
  (def exact->inexact (number? . -> . inexact?)
    #:refinements
    (real? . -> . real?)
    (integer? . -> . integer?))
  (def real->single-flonum (real? . -> . single-flonum?))
  (def real->double-flonum (real? . -> . flonum?))

;;;;; 4.2.2 Generic Numerics

  ;; 4.2.2.1 Arithmetic
  (def +
    (() #:rest (listof number?)  . ->* . number?)
    #:refinements
    (() #:rest (listof exact-positive-integer?) . ->* . exact-positive-integer?)
    (() #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
    (() #:rest (listof exact-integer?) . ->* . exact-integer?)
    (() #:rest (listof integer?) . ->* . integer?)
    (() #:rest (listof real?) . ->* . real?)
    (() #:rest (listof (>=/c 0)) . ->* . (>=/c 0))
    #;(() #:rest (listof (not/c positive?)) . ->* . (not/c positive?)))
  (def - (number? number? . -> . number?)
    ; FIXME var-args and precise refinement for first case
    #:refinements
    (exact-positive-integer? (=/c 1) . -> . exact-nonnegative-integer?)
    (exact-integer? exact-integer? . -> . exact-integer?)
    (integer? integer? . -> . integer?)
    (real? real? . -> . real?)
    ((<=/c 0) (>=/c 0) . -> . (<=/c 0))
    ((>=/c 0) (<=/c 0) . -> . (>=/c 0)))
  #;(def -
      ((number?) #:rest (listof number?) . ->* . number?)
      #:refinements
      ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
      ((integer?) #:rest (listof integer?) . ->* . integer?)
      ((real?) #:rest (listof real?) . ->* . real?))
  (def *
    (() #:rest (listof number?) . ->* . number?)
    #:refinements
    (() #:rest (listof exact-positive-integer?) . ->* . exact-positive-integer?)
    (() #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
    (() #:rest (listof exact-integer?) . ->* . exact-integer?)
    (() #:rest (listof integer?) . ->* . integer?)
    (() #:rest (listof real?) . ->* . real?)
    (() #:rest (listof (>=/c 1)) . ->* . (>=/c 1))
    (() #:rest (listof (>=/c 0)) . ->* . (>=/c 0)))
  (def /
    ((number?) #:rest (listof (and/c number? (or/c inexact? (not/c zero?)))) . ->* . number?)
    #:refinements
    ((real?) #:rest (listof real?) . ->* . real?)
    (((not/c zero?)) #:rest list? . ->* . (not/c zero?)))
  (def* (quotient remainder modulo) ; FIXME: only error on exact 0
    (integer? (and/c integer? (not/c zero?)) . -> . integer?))
  (def quotient/remainder
    (integer? (and/c integer? (not/c zero?)) . -> . (values integer? integer?)))
  (def add1
    (number? . -> . number?)
    #:refinements
    (integer? . -> . integer?)
    (real? . -> . real?)
    (exact? . -> . exact?)
    (inexact? . -> . inexact?)
    (exact-nonnegative-integer? . -> . exact-positive-integer?)
    (exact-positive-integer? . -> . exact-positive-integer?)
    (exact-integer? . -> . exact-integer?)
    ((not/c negative?) . -> . positive?)
    (positive? . -> . positive?))
  (def sub1
    (number? . -> . number?)
    #:refinements
    (exact-positive-integer? . -> . exact-nonnegative-integer?)
    (exact-nonnegative-integer? . -> . exact-integer?)
    (exact-integer? . -> . exact-integer?)
    (integer? . -> . integer?)
    (real? . -> . real?))
  (def abs
    (real? . -> . real?)
    #:refinements
    (integer? . -> . integer?))
  (def max ((real?) #:rest (listof real?) . ->* . real?)
    #:refinements
    ((exact-positive-integer?) #:rest (listof exact-integer?) . ->* . exact-positive-integer?)
    ((exact-nonnegative-integer?) #:rest (listof exact-integer?) . ->* . exact-nonnegative-integer?)
    ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
    ((integer?) #:rest (listof integer?) . ->* . integer?))
  (def min ((real?) #:rest (listof real?) . ->* . real?)
    #:refinements
    ((exact-nonnegative-integer?) #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
    ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
    ((integer?) #:rest (listof integer?) . ->* . integer?))
  (def* (gcd lcm) ((real?) #:rest (listof real?) . ->* . real?))
  (def* (round floor ceiling truncate)
    (real? . -> . (or/c integer? +inf.0 -inf.0 +nan.0)))
  (def* (numerator denominator) (rational? . -> . integer?))
  (def rationalize (real? real? . -> . real?))

  ;; 4.2.2.2 Number Comparison
  ; FIXME varargs
  (def-pred = (number? number?)) 
  (def-preds (< <= > >=) (real? real?))

  ;; 4.2.2.3 Powers and Roots
  (def sqrt (number? . -> . number?)
    #:refinements
    ((>=/c 0) . -> . (>=/c 0)))
  (def integer-sqrt (integer? . -> . number?))
  #;(integer-sqrt/remainder ; FIXME
     (integer? . -> . number? integer?))
  (def expt (number? number? . -> . number?)
    #|#:other-errors
    (zero? negative?)|#)
  (def exp (number? . -> . number?))
  (def log (number? . -> . number?))

  ;; 4.2.2.4 Trigonometric Functions
  (def* (sin cos tan asin acos atan) (number? . -> . number?)
    #:refinements
    (real? . -> . real?))

  ;; 4.2.2.5 Complex Numbers
  (def* (make-rectangular make-polar) (real? real? . -> . number?))
  (def* (real-part imag-part) (number? . -> . real?))
  (def magnitude (number? . -> . (and/c real? (not/c negative?))))
  (def angle (number? . -> . real?))

  ;; 4.2.2.6 Bitwise Operations
  (def* (bitwise-ior bitwise-and bitwise-xor)
    ((exact-integer? exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?))
  (def bitwise-not (exact-integer? . -> . exact-integer?))
  (def-pred bitwise-bit-set? (exact-integer? exact-nonnegative-integer?))
  (def bitwise-bit-field ; FIXME `start ≤ end`
    (exact-integer? exact-nonnegative-integer? exact-nonnegative-integer? . -> . integer?))
  (def arithmetic-shift
    (exact-integer? exact-integer? . -> . exact-integer?))
  (def integer-length ; TODO post-con more precise than doc. Confirm.
    (exact-integer? . -> . exact-nonnegative-integer?))

  ;; 4.2.2.7 Random Numbers
  (def random ; FIXME all uses. Full cases are not 1st-orderly distinguishable
    (case->
     [-> (and/c inexact-real? (>/c 0) (</c 1))]
     [exact-nonnegative-integer? . -> . exact-nonnegative-integer?]
     [exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?]))
  (def random-seed ((and/c exact-integer? positive?) . -> . void?))
  (def make-pseudo-random-generator (-> pseudo-random-generator?))
  (def-pred pseudo-random-generator?)
  (def current-pseudo-random-generator ; FIXME parameter
    (-> pseudo-random-generator?))
  (def pseudo-random-generator->vector
    (pseudo-random-generator? . -> . pseudo-random-generator-vector?))
  (def vector->pseudo-random-generator
    (pseudo-random-generator-vector? . -> . pseudo-random-generator?))
  (def vector->pseudo-random-generator!
    (pseudo-random-generator? pseudo-random-generator-vector? . -> . void?))
  (def-pred pseudo-random-generator-vector?)

  ;; 4.2.2.8 System-Provided Randomness
  #;(def crypto-random-bytes
      (exact-positive-integer? . -> . bytes?))

  ;; 4.2.2.9 Number-String Conversions
  (def number->string ; FIXME uses
    (number? . -> . string?))
  (def string->number ; FIXME uses
    (string? . -> . (or/c number? not)))
  (def real->decimal-string ; FIXME uses
    (real? exact-nonnegative-integer? . -> . string?))
  (def integer-bytes->integer ; FIXME uses
    (bytes? any/c . -> . exact-integer?))
  (def integer->integer-bytes ; FIXME uses
    (exact-integer? (or/c 2 4 8) any/c . -> . bytes?))
  (def floating-point-bytes->real ; FIXME uses
    (bytes? . -> . flonum?))
  (def real->floating-point-bytes ; FIXME uses
    (real? (or/c 2 4 8) . -> . bytes?))
  (def system-big-endian? ; FIXME: opaque or machine dependent? (former probably)
    (-> boolean?))

  ;; 4.2.2.10 Extra Functions
  (def-const pi)
  (def-const pi.f)
  (def* (degrees->radians radians->degrees) (real? . -> . real?))
  (def sqr (number? . -> . number?)
    #:refinements
    (real? . -> . (>=/c 0))
    (integer? . -> . integer?))
  (def sgn (real? . -> . (or/c -1 0 1 +nan.0 +nan.f)))
  (def conjugate (number? . -> . number?))
  (def* (sinh cosh tanh) (number? . -> . number?))
  (def* (exact-round exact-floor exact-ceiling exact-truncate) (rational? . -> . exact-integer?))
  (def order-of-magnitude ((and/c real? positive?) . -> . exact-integer?))
  (def-preds (nan? infinite?) (real?))

;;;;; 4.2.3 Flonums
  (def* (fl+ fl- fl*) (flonum? flonum? . -> . flonum?))
  (def fl/ (flonum? (and/c flonum? (not/c zero?)) . -> . flonum?))
  (def flabs (flonum? . -> . (and/c flonum? (not/c negative?))))
  (def-preds (fl= fl< fl> fl<= fl>=) (flonum? flonum?))
  (def* (flmin flmax) (flonum? flonum? . -> . flonum?))
  (def* (flround flfloor flceiling fltruncate) (flonum? . -> . flonum?))
  (def* (flsin flcos fltan flasin flacos flatan fllog flexp flsqrt) (flonum? . -> . flonum?))
  (def flexpt ; FIXME accurate behavior for abstract +inf +nan shits
    (flonum? flonum? . -> . flonum?))
  (def ->fl (exact-integer? . -> . flonum?))
  (def fl->exact-integer (flonum? . -> . exact-integer?))
  (def make-flrectangular ; FIXME precision
    (flonum? flonum? . -> . number?))
  (def* (flreal-part flimag-part) ; FIXME correct domain
    (float-complex? . -> . flonum?))
  (def flrandom ; FIXME range
    (pseudo-random-generator? . -> . flonum?))

  ;; 4.2.3.2 Flonum Vectors
  #|
  (def-pred flvector?)
  #;(flvector
     (-> flvector?))
  (def make-flvector ; FIXME uses
    (exact-nonnegative-integer? flonum? . -> . flvector?))
  (def flvector-length (flvector? . -> . exact-nonnegative-integer?))
  (def flvector-ref (flvector? exact-nonnegative-integer? . -> . flonum?))
  (def flvector-set! (flvector? exact-nonnegative-integer? flonum? . -> . flonum?))
  (def flvector-copy ; FIXME uses
    (flvector? . -> . flvector?))
  (def in-flvector ; FIXME uses
    (flvector? . -> . sequence?))
  #;(shared-flvector
     (-> flvector?))
  (def make-shared-flvector ; FIXME uses
    (exact-nonnegative-integer? flonum? . -> . flvector?))
  |#

;;;;; 4.2.4 Fixnums

  ;; 4.1.4.1 Fixnum Arithmetic
  (def* (fx+ fx- fx*) (fixnum? fixnum? . -> . fixnum?))
  (def* (fxquotient fxremainder fxmodulo) (fixnum? (and/c fixnum? (not/c zero?)) . -> . fixnum?))
  (def fxabs (fixnum? . -> . fixnum?))
  (def* (fxand fxior fxxor) (fixnum? fixnum? . -> . fixnum?))
  (def fxnot (fixnum? . -> . fixnum?))
  (def* (fxlshift fxrshift) (fixnum? fixnum? . -> . fixnum?))
  (def-preds (fx= fx< fx> fx<= fx>=) (fixnum? fixnum?))
  (def* (fxmin fxmax) (fixnum? fixnum? . -> . fixnum?))
  (def fx->fl (fixnum? . -> . flonum?))
  (def fl->fx (flonum? . -> . fixnum?))

  ;; 4.2.4.2 Fixnum Vectors
  #|
  (def-pred fxvector?)
  #;(fxvector
     (-> fxvector?))
  (def make-fxvector ; FIXME uses
    (exact-nonnegative-integer? fixnum? . -> . fxvector?))
  (def fxvector-length (fxvector? . -> . exact-nonnegative-integer?))
  (def fxvector-ref (fxvector? exact-nonnegative-integer? . -> . fixnum?))
  (def fxvector-set! (fxvector? exact-nonnegative-integer? fixnum? . -> . fixnum?))
  (def fxvector-copy ; FIXME uses
    (fxvector? . -> . fxvector?))
  (def in-fxvector ; FIXME uses
    (fxvector? . -> . sequence?))
  #;(shared-fxvector
     (-> fxvector?))
  (def make-shared-fxvector ; FIXME uses
    (exact-nonnegative-integer? fixnum? . -> . fxvector?))
  |#

  ;;;;; 4.2.5 Extflonums
  (def-pred extflonum?)
  (def extflonum-available? (-> boolean?))

  ;; Extflonum Arithmetic
  (def* (extfl+ extfl- extfl*) (extflonum? extflonum? . -> . extflonum?))
  (def extfl/ (extflonum? extflonum? . -> . extflonum?))
  (def extflabs (extflonum? . -> . extflonum?))
  (def-preds (extfl= extfl< extfl> extfl<= extfl>=) (extflonum? extflonum?))
  (def* (extflmin extflmax) (extflonum? extflonum? . -> . extflonum?))
  (def* (extflround extflfloor extflceiling extfltruncate) (extflonum? . -> . extflonum?))
  (def* (extflsin extflcos extfltan extflasin extflacos extflatan extfllog extflexp extflsqrt)
    (extflonum? . -> . extflonum?))
  (def extflexpt (extflonum? extflonum? . -> . extflonum?))
  (def ->extfl (exact-integer? . -> . extflonum?))
  (def extfl->exact-integer (extflonum? . -> . exact-integer?))
  (def real->extfl (real? . -> . extflonum?))
  (def extfl->exact (extflonum? . -> . (and/c real? exact?)))
  (def extfl->inexact (extflonum? . -> . flonum?))

  ;; 4.2.5.2 Extflonum Constants
  (def-const pi.t)

  ;; 4.2.5.3 Extflonum Vectors
  (def-pred extflvector?)
  #;(extflvector
     (-> extflvector?))
  (def make-extflvector ; FIXME uses
    (exact-nonnegative-integer? extflonum? . -> . extflvector?))
  (def extflvector-length (extflvector? . -> . exact-nonnegative-integer?))
  (def extflvector-ref (extflvector? exact-nonnegative-integer? . -> . extflonum?))
  (def extflvector-set! (extflvector? exact-nonnegative-integer? extflonum? . -> . extflonum?))
  (def extflvector-copy ; FIXME uses
    (extflvector? . -> . extflvector?))
  (def in-extflvector (extflvector? . -> . sequence?))
  (def make-shared-extflvector (exact-nonnegative-integer? . -> . extflvector?))

  ;; 4.2.5.4 Extflonum Byte Strings
  (def floating-point-bytes->extfl ; FIXME uses
    (bytes? . -> . extflonum?))
  (def extfl->floating-point-bytes (extflonum? . -> . bytes?))
  )
