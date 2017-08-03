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
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.2 Numbers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-02@
  (import prim-runtime^ proof-system^ widening^ val^ pc^)
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
  (def-prim inexact->exact (number? . -> . exact?))
  (def-prim exact->inexact (number? . -> . inexact?)
    #:refinements
    (real? . -> . real?)
    (integer? . -> . integer?))
  (def-prim real->single-flonum (real? . -> . single-flonum?))
  (def-prim real->double-flonum (real? . -> . flonum?))

;;;;; 4.2.2 Generic Numerics

  ;; 4.2.2.1 Arithmetic
  (def-prim +
    (() #:rest (listof number?)  . ->* . number?)
    #:refinements
    (() #:rest (listof exact-positive-integer?) . ->* . exact-positive-integer?)
    (() #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
    (() #:rest (listof exact-integer?) . ->* . exact-integer?)
    (() #:rest (listof integer?) . ->* . integer?)
    (() #:rest (listof real?) . ->* . real?)
    (() #:rest (listof (>=/c 0)) . ->* . (>=/c 0))
    #;(() #:rest (listof (not/c positive?)) . ->* . (not/c positive?)))
  (def-prim - (number? number? . -> . number?)
    ; FIXME var-args and precise refinement for first case
    #:refinements
    (exact-positive-integer? (=/c 1) . -> . exact-nonnegative-integer?)
    (exact-integer? exact-integer? . -> . exact-integer?)
    (integer? integer? . -> . integer?)
    (real? real? . -> . real?)
    ((<=/c 0) (>=/c 0) . -> . (<=/c 0))
    ((>=/c 0) (<=/c 0) . -> . (>=/c 0)))
  #;(def-prim -
      ((number?) #:rest (listof number?) . ->* . number?)
      #:refinements
      ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
      ((integer?) #:rest (listof integer?) . ->* . integer?)
      ((real?) #:rest (listof real?) . ->* . real?))
  (def-prim *
    (() #:rest (listof number?) . ->* . number?)
    #:refinements
    (() #:rest (listof exact-positive-integer?) . ->* . exact-positive-integer?)
    (() #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
    (() #:rest (listof exact-integer?) . ->* . exact-integer?)
    (() #:rest (listof integer?) . ->* . integer?)
    (() #:rest (listof real?) . ->* . real?)
    (() #:rest (listof (>=/c 1)) . ->* . (>=/c 1))
    (() #:rest (listof (>=/c 0)) . ->* . (>=/c 0)))
  (def-prim /
    ((number?) #:rest (listof (and/c number? (or/c inexact? (not/c zero?)))) . ->* . number?)
    #:refinements
    ((real?) #:rest (listof real?) . ->* . real?)
    (((not/c zero?)) #:rest list? . ->* . (not/c zero?)))
  (def-prims (quotient remainder modulo) ; FIXME: only error on exact 0
    (integer? (and/c integer? (not/c zero?)) . -> . integer?))
  #;(def-prims quotient/remainder ; TODO
      (integer? (and/c integer? (not/c zero?)) . -> . (values integer? integer?)))
  (def-prim add1
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
  (def-prim sub1
    (number? . -> . number?)
    #:refinements
    (exact-positive-integer? . -> . exact-nonnegative-integer?)
    (exact-nonnegative-integer? . -> . exact-integer?)
    (exact-integer? . -> . exact-integer?)
    (integer? . -> . integer?)
    (real? . -> . real?))
  (def-prim abs
    (real? . -> . real?)
    #:refinements
    (integer? . -> . integer?))
  (def-prim max ((real?) #:rest (listof real?) . ->* . real?)
    #:refinements
    ((exact-positive-integer?) #:rest (listof exact-integer?) . ->* . exact-positive-integer?)
    ((exact-nonnegative-integer?) #:rest (listof exact-integer?) . ->* . exact-nonnegative-integer?)
    ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
    ((integer?) #:rest (listof integer?) . ->* . integer?))
  (def-prim min ((real?) #:rest (listof real?) . ->* . real?)
    #:refinements
    ((exact-nonnegative-integer?) #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
    ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
    ((integer?) #:rest (listof integer?) . ->* . integer?))
  (def-prims (gcd lcm) ((real?) #:rest (listof real?) . ->* . real?))
  (def-prims (round floor ceiling truncate)
    (real? . -> . (or/c integer? +inf.0 -inf.0 +nan.0)))
  (def-prims (numerator denominator) (rational? . -> . integer?))
  (def-prim rationalize (real? real? . -> . real?))

  ;; 4.2.2.2 Number Comparison
  ; FIXME varargs
  (def-pred = (number? number?)) 
  (def-preds (< <= > >=) (real? real?))

  ;; 4.2.2.3 Powers and Roots
  (def-prim sqrt (number? . -> . number?)
    #:refinements
    ((>=/c 0) . -> . (>=/c 0)))
  (def-prim integer-sqrt (integer? . -> . number?))
  #;(integer-sqrt/remainder ; FIXME
     (integer? . -> . number? integer?))
  (def-prim expt (number? number? . -> . number?)
    #:other-errors
    (zero? negative?))
  (def-prim exp (number? . -> . number?))
  (def-prim log (number? . -> . number?))

  ;; 4.2.2.4 Trigonometric Functions
  (def-prims (sin cos tan asin acos atan) (number? . -> . number?)
    #:refinements
    (real? . -> . real?))

  ;; 4.2.2.5 Complex Numbers
  (def-prims (make-rectangular make-polar) (real? real? . -> . number?))
  (def-prims (real-part imag-part) (number? . -> . real?))
  (def-prim magnitude (number? . -> . (and/c real? (not/c negative?))))
  (def-prim angle (number? . -> . real?))

  ;; 4.2.2.6 Bitwise Operations
  (def-prims (bitwise-ior bitwise-and bitwise-xor)
    ((exact-integer? exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?))
  (def-prim bitwise-not (exact-integer? . -> . exact-integer?))
  (def-pred bitwise-bit-set? (exact-integer? exact-nonnegative-integer?))
  (def-prim bitwise-bit-field ; FIXME `start ≤ end`
    (exact-integer? exact-nonnegative-integer? exact-nonnegative-integer? . -> . integer?))
  (def-prim arithmetic-shift
    (exact-integer? exact-integer? . -> . exact-integer?))
  (def-prim integer-length ; TODO post-con more precise than doc. Confirm.
    (exact-integer? . -> . exact-nonnegative-integer?))

  ;; 4.2.2.7 Random Numbers
  (def-prim/custom (random ⟪ℋ⟫ ℓ Σ $ Γ Ws) ; FIXME all uses
    (match Ws
      ['()
       (define Vₐ (+● 'real? 'inexact? (->/c 0) (-</c 1)))
       {set (-ΓA Γ (-W (list Vₐ) (-t.@ 'random '())))}]
      [(list W) ; FIXME check W
       (define Vₐ (+● 'exact-nonnegative-integer?))
       {set (-ΓA Γ (-W (list Vₐ) (?t@ 'random (-W¹-t W))))}]
      [_
       (define blm (blm-arity ℓ 'random (list 0 1) (map -W¹-V Ws)))
       {set (-ΓA Γ blm)}]))
  (def-prim/todo random-seed
    ((and/c exact-integer? positive?) . -> . void?))
  (def-prim/todo make-pseudo-random-generator (-> pseudo-random-generator?))
  (def-pred pseudo-random-generator?)
  (def-prim/todo current-pseudo-random-generator ; FIXME parameter
    (-> pseudo-random-generator?))
  (def-prim/todo pseudo-random-generator->vector
    (pseudo-random-generator? . -> . pseudo-random-generator-vector?))
  (def-prim/todo vector->pseudo-random-generator
    (pseudo-random-generator-vector? . -> . pseudo-random-generator?))
  (def-prim/todo vector->pseudo-random-generator!
    (pseudo-random-generator? pseudo-random-generator-vector? . -> . void?))
  (def-pred/todo pseudo-random-generator-vector?)

  ;; 4.2.2.8 System-Provided Randomness
  #;(def-prim/todo crypto-random-bytes
      (exact-positive-integer? . -> . bytes?))

  ;; 4.2.2.9 Number-String Conversions
  (def-prim number->string ; FIXME uses
    (number? . -> . string?))
  (def-prim string->number ; FIXME uses
    (string? . -> . (or/c number? not)))
  (def-prim real->decimal-string ; FIXME uses
    (real? exact-nonnegative-integer? . -> . string?))
  (def-prim integer-bytes->integer ; FIXME uses
    (bytes? any/c . -> . exact-integer?))
  (def-prim integer->integer-bytes ; FIXME uses
    (exact-integer? (or/c 2 4 8) any/c . -> . bytes?))
  (def-prim floating-point-bytes->real ; FIXME uses
    (bytes? . -> . flonum?))
  (def-prim real->floating-point-bytes ; FIXME uses
    (real? (or/c 2 4 8) . -> . bytes?))
  (def-prim system-big-endian? ; FIXME: opaque or machine dependent? (former probably)
    (-> boolean?))

  ;; 4.2.2.10 Extra Functions
  (def-const pi)
  (def-const pi.f)
  (def-prims (degrees->radians radians->degrees) (real? . -> . real?))
  (def-prim sqr (number? . -> . number?)
    #:refinements
    (real? . -> . (>=/c 0))
    (integer? . -> . integer?))
  (def-prim sgn (real? . -> . (or/c -1 0 1 +nan.0 +nan.f)))
  (def-prim conjugate (number? . -> . number?))
  (def-prims (sinh cosh tanh) (number? . -> . number?))
  (def-prims (exact-round exact-floor exact-ceiling exact-truncate) (rational? . -> . exact-integer?))
  (def-prim order-of-magnitude ((and/c real? positive?) . -> . exact-integer?))
  (def-preds (nan? infinite?) (real?))

;;;;; 4.2.3 Flonums
  (def-prims (fl+ fl- fl*) (flonum? flonum? . -> . flonum?))
  (def-prim fl/ (flonum? (and/c flonum? (not/c zero?)) . -> . flonum?))
  (def-prim flabs (flonum? . -> . (and/c flonum? (not/c negative?))))
  (def-preds (fl= fl< fl> fl<= fl>=) (flonum? flonum?))
  (def-prims (flmin flmax) (flonum? flonum? . -> . flonum?))
  (def-prims (flround flfloor flceiling fltruncate) (flonum? . -> . flonum?))
  (def-prims (flsin flcos fltan flasin flacos flatan fllog flexp flsqrt) (flonum? . -> . flonum?))
  (def-prim flexpt ; FIXME accurate behavior for abstract +inf +nan shits
    (flonum? flonum? . -> . flonum?))
  (def-prim ->fl (exact-integer? . -> . flonum?))
  (def-prim fl->exact-integer (flonum? . -> . exact-integer?))
  (def-prim make-flrectangular ; FIXME precision
    (flonum? flonum? . -> . number?))
  (def-prims (flreal-part flimag-part) ; FIXME correct domain
    (complex? . -> . flonum?))
  (def-prim flrandom ; FIXME range
    (pseudo-random-generator? . -> . flonum?))

  ;; 4.2.3.2 Flonum Vectors
  (def-pred flvector?)
  #;(flvector
     (-> flvector?))
  (def-prim/todo make-flvector ; FIXME uses
    (exact-nonnegative-integer? flonum? . -> . flvector?))
  (def-prim/todo flvector-length (flvector? . -> . exact-nonnegative-integer?))
  (def-prim/todo flvector-ref (flvector? exact-nonnegative-integer? . -> . flonum?))
  (def-prim/todo flvector-set! (flvector? exact-nonnegative-integer? flonum? . -> . flonum?))
  (def-prim/todo flvector-copy ; FIXME uses
    (flvector? . -> . flvector?))
  (def-prim/todo in-flvector ; FIXME uses
    (flvector? . -> . sequence?))
  #;(shared-flvector
     (-> flvector?))
  (def-prim/todo make-shared-flvector ; FIXME uses
    (exact-nonnegative-integer? flonum? . -> . flvector?))

;;;;; 4.2.4 Fixnums

  ;; 4.1.4.1 Fixnum Arithmetic
  (def-prims (fx+ fx- fx*) (fixnum? fixnum? . -> . fixnum?))
  (def-prims (fxquotient fxremainder fxmodulo) (fixnum? (and/c fixnum? (not/c zero?)) . -> . fixnum?))
  (def-prim fxabs (fixnum? . -> . fixnum?))
  (def-prims (fxand fxior fxxor) (fixnum? fixnum? . -> . fixnum?))
  (def-prim fxnot (fixnum? . -> . fixnum?))
  (def-prims (fxlshift fxrshift) (fixnum? fixnum? . -> . fixnum?))
  (def-preds (fx= fx< fx> fx<= fx>=) (fixnum? fixnum?))
  (def-prims (fxmin fxmax) (fixnum? fixnum? . -> . fixnum?))
  (def-prim fx->fl (fixnum? . -> . flonum?))
  (def-prim fl->fx (flonum? . -> . fixnum?))

  ;; 4.2.4.2 Fixnum Vectors
  (def-pred fxvector?)
  #;(fxvector
     (-> fxvector?))
  (def-prim/todo make-fxvector ; FIXME uses
    (exact-nonnegative-integer? fixnum? . -> . fxvector?))
  (def-prim/todo fxvector-length (fxvector? . -> . exact-nonnegative-integer?))
  (def-prim/todo fxvector-ref (fxvector? exact-nonnegative-integer? . -> . fixnum?))
  (def-prim/todo fxvector-set! (fxvector? exact-nonnegative-integer? fixnum? . -> . fixnum?))
  (def-prim/todo fxvector-copy ; FIXME uses
    (fxvector? . -> . fxvector?))
  (def-prim/todo in-fxvector ; FIXME uses
    (fxvector? . -> . sequence?))
  #;(shared-fxvector
     (-> fxvector?))
  (def-prim/todo make-shared-fxvector ; FIXME uses
    (exact-nonnegative-integer? fixnum? . -> . fxvector?))

;;;;; 4.2.5 Extflonums
  (def-pred extflonum?)
  (def-prim extflonum-available? (-> boolean?))

  ;; Extflonum Arithmetic
  (def-prims (extfl+ extfl- extfl*) (extflonum? extflonum? . -> . extflonum?))
  (def-prim extfl/ (extflonum? extflonum? . -> . extflonum?))
  (def-prim extflabs (extflonum? . -> . extflonum?))
  (def-preds (extfl= extfl< extfl> extfl<= extfl>=) (extflonum? extflonum?))
  (def-prims (extflmin extflmax) (extflonum? extflonum? . -> . extflonum?))
  (def-prims (extflround extflfloor extflceiling extfltruncate) (extflonum? . -> . extflonum?))
  (def-prims (extflsin extflcos extfltan extflasin extflacos extflatan extfllog extflexp extflsqrt)
    (extflonum? . -> . extflonum?))
  (def-prim extflexpt (extflonum? extflonum? . -> . extflonum?))
  (def-prim ->extfl (exact-integer? . -> . extflonum?))
  (def-prim extfl->exact-integer (extflonum? . -> . exact-integer?))
  (def-prim real->extfl (real? . -> . extflonum?))
  (def-prim extfl->exact (extflonum? . -> . (and/c real? exact?)))
  (def-prim extfl->inexact (extflonum? . -> . flonum?))

  ;; 4.2.5.2 Extflonum Constants
  (def-const pi.t)

  ;; 4.2.5.3 Extflonum Vectors
  (def-pred extflvector?)
  #;(extflvector
     (-> extflvector?))
  (def-prim/todo make-extflvector ; FIXME uses
    (exact-nonnegative-integer? extflonum? . -> . extflvector?))
  (def-prim/todo extflvector-length (extflvector? . -> . exact-nonnegative-integer?))
  (def-prim/todo extflvector-ref (extflvector? exact-nonnegative-integer? . -> . extflonum?))
  (def-prim/todo extflvector-set! (extflvector? exact-nonnegative-integer? extflonum? . -> . extflonum?))
  (def-prim/todo extflvector-copy ; FIXME uses
    (extflvector? . -> . extflvector?))
  (def-prim/todo in-extflvector (extflvector? . -> . sequence?))
  (def-prim/todo make-shared-extflvector (exact-nonnegative-integer? . -> . extflvector?))

  ;; 4.2.5.4 Extflonum Byte Strings
  (def-prim/todo floating-point-bytes->extfl ; FIXME uses
    (bytes . -> . extflonum?))
  (def-prim/todo extfl->floating-point-bytes (extflonum? . -> . bytes?))
  )
