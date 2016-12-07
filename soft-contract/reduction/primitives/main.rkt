#lang typed/racket/base

;; This module defines primitive operations on first-order data,
;; each of which is an atomic operation that can be perform in 1 "step",
;; returning a set of possible answers paired with path-conditions.
;; 
;; First-order "library functions" and "primitives", as far as this tool is concerned, are the same.
;; A higher-order function, however, can invoke behavioral values fed to it arbitrarily,
;; and must be approximated by `havoc`, thus is not an "atomic" operation
;; definable in this module.
(provide (all-defined-out))

(require racket/contract
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
         racket/struct
         math/base
         "../../utils/list.rkt"
         "../../ast/definition.rkt"
         "../../runtime/definition.rkt"
         "../../runtime/simp.rkt"
         "utils.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.1 Booleans and Equality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-pred boolean?)
(def-pred not)

(def-prims (equal? eqv? eq?) (any/c any/c . -> . any/c))
; equal?/recur
(def-pred immutable?)
(def-opq prop:equal+hash any/c)

(def-const true)
(def-const false)
(def-prim symbol=? (symbol? symbol? . -> . boolean?))
(def-prim boolean=? (boolean? boolean? . -> . boolean?))
(def-alias false? not)
(def-prim xor (any/c any/c . -> . any/c))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.2 Numbers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(def-prim exact->inexact (number? . -> . inexact?))
(def-prim real->single-flonum (real? . -> . single-flonum?))
(def-prim real->double-flonum (real? . -> . flonum?))

;;;;; 4.2.2 Generic Numerics

;; 4.2.2.1 Arithmetic
(def-prim + ; FIXME varargs
  (number? number? . -> . number?)
  #:refinements
  (exact-positive-integer? exact-positive-integer? . -> . exact-positive-integer?)
  (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)
  (exact-integer? exact-integer? . -> . exact-integer?)
  (integer? integer? . -> . integer?)
  (real? real? . -> . real?)
  (positive? (not/c negative?) . -> . positive?)
  ((not/c negative?) positive? . -> . positive?)
  (negative? (not/c positive?) . -> . negative?)
  ((not/c positive?) negative? . -> . negative?)
  ((not/c negative?) (not/c negative?) . -> . (not/c negative?))
  ((not/c positive?) (not/c positive?) . -> . (not/c positive?)))
(def-prim - ; FIXME varargs
 (number? number? . -> . number?)
 #:refinements
 (exact-positive-integer? (=/c 1) . -> . exact-nonnegative-integer?)
 (exact-integer? exact-integer? . -> . exact-integer?)
 (integer? integer? . -> . integer?)
 (real? real? . -> . real?))
(def-prim * ; FIXME varargs
 (number? number? . -> . number?)
 #:refinements
 (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?)
 (exact-integer? exact-integer? . -> . exact-integer?)
 (integer? integer? . -> . integer?)
 (real? real? . -> . real?))
(def-prim / ; FIXME varargs
 (number? (and/c number? (or/c inexact? (not/c zero?))) . -> . number?)
 #:refinements
 (real? real? . -> . real?)
 ((not/c zero?) any/c . -> . (not/c zero?)))
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
 ((not/c negative?) . -> . positive?)
 (positive? . -> . positive?))
(def-prim sub1
 (number? . -> . number?)
 #:refinements
 (integer? . -> . integer?)
 (real? . -> . real?))
(def-prim abs
 (real? . -> . real?)
 #:refinements
 (integer? . -> . integer?))
(def-prims (max min) ; FIXME varargs
 (real? real? . -> . real?)
 #:refinements
 (exact-nonnegative-integer?  exact-nonnegative-integer? . -> . exact-nonnegative-integer?)
 (integer? integer? . -> . integer?))
(def-prims (gcd lcm) ; FIXME varargs
 (rational? rational? . -> . rational?))
(def-prims (round floor ceiling truncate)
 (real? . -> . (or/c integer? +inf.0 -inf.0 +nan.0)))
(def-prims (numerator denominator)
 (rational? . -> . integer?))
(def-prim rationalize
 (real? real? . -> . real?))

;; 4.2.2.2 Number Comparison
; FIXME varargs
(def-pred = (number? number?)) 
(def-prims (< <= > >=) (real? real? . -> . boolean?))

;; 4.2.2.3 Powers and Roots
(def-prim sqrt (number? . -> . number?))
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
(def-prims (bitwise-ior bitwise-and bitwise-xor) ; FIXME varargs
 (exact-integer? exact-integer? . -> . exact-integer?))
(def-prim bitwise-not (exact-integer? . -> . exact-integer?))
(def-prim bitwise-bit-set? (exact-integer? exact-nonnegative-integer? . -> . boolean?))
(def-prim bitwise-bit-field ; FIXME `start ≤ end`
 (exact-integer? exact-nonnegative-integer? exact-nonnegative-integer? . -> . integer?))
(def-prim arithmetic-shift
 (exact-integer? exact-integer? . -> . exact-integer?))
(def-prim integer-length ; TODO post-con more precise than doc. Confirm.
 (exact-integer? . -> . exact-nonnegative-integer?))

;; 4.2.2.7 Random Numbers
(def-prim random ; FIXME range, all uses
 (integer? . -> . exact-nonnegative-integer?))
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
  (real? . -> . real?)
  (integer? . -> . integer?))
(def-prim sgn (real? . -> . (or/c -1 0 1 +nan.0 +nan.f)))
(def-prim conjugate (number? . -> . number?))
(def-prims (sinh cosh tanh) (number? . -> . number?))
(def-prims (exact-round exact-floor exact-ceiling exact-truncate) (rational? . -> . exact-integer?))
(def-prim order-of-magnitude ((and/c real? positive?) . -> . exact-integer?))
(def-prims (nan? infinite?) (real? . -> . boolean?))

;;;;; 4.2.3 Flonums
(def-prims (fl+ fl- fl*) (flonum? flonum? . -> . flonum?))
(def-prim fl/ (flonum? (and/c flonum? (not/c zero?)) . -> . flonum?))
(def-prim flabs (flonum? . -> . (and/c flonum? (not/c negative?))))
(def-prims (fl= fl< fl> fl<= fl>=) (flonum? flonum? . -> . boolean?))
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
 (float-complex? . -> . flonum?))
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
(def-prims (fx= fx< fx> fx<= fx>=) (fixnum? fixnum? . -> . boolean?))
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
(def-prims (extfl= extfl< extfl> extfl<= extfl>=) (extflonum? extflonum? . -> . boolean?))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.3 Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 4.3.1 Constructors, Selectors, Mutators
(def-pred string?)
(def-prim make-string ; FIXME all uses
 (exact-nonnegative-integer? char? . -> . (and/c string? (not/c immutable?))))
(def-prim/todo string
 (() #:rest (listof char?) . ->* . string?))
(def-prim string->immutable-string
 (string? . -> . (and/c string? immutable?)))
(def-prim string-length
 (string? . -> . exact-nonnegative-integer?))
(def-prim string-ref
 (string? exact-nonnegative-integer? . -> . char?))
(def-prim string-set!
 ((and/c string? (not/c immutable?)) exact-nonnegative-integer? char? . -> . void?))
(def-prim substring ; FIXME uses
 (string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?))
(def-prim string-copy
 (string . -> . string?))
(def-prim/todo string-copy! ; FIXME uses
 ((and/c string? (not/c immutable?)) exact-nonnegative-integer? string? . -> . void?))
(def-prim/todo string-fill! ; FIXME uses
 ((and/c string? (not/c immutable?)) char? . -> . void?))
(def-prim/todo string-append ; FIXME listof
 (() #:rest (listof string?) . ->* . string?))
(def-prim/todo string->list ; FIXME listof
 (string? . -> . (listof char?)))
(def-prim/todo list->string ; FIXME listof
 ((listof char?) . -> . string?))
(def-prim/todo build-string
 (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . char?) . -> . string?))

;; 4.3.2 String Comparisons. FIXME varargs
(def-prims (string=? string<? string<=? string>? string>=?
            string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?)
 (string? string? . -> . boolean?))

;; 4.3.3 String Conversions
(def-prims (string-upcase string-downcase string-titlecase string-foldcase
            string-normalize-nfd string-normalize-nfkd
            string-normalize-nfc string-normalize-nfkc)
 (string? . -> . string?))

;; 4.3.4 Locale-specific string operations 
; FIXME varargs
(def-prims (string-locale=? string-locale<? string-locale>?
            string-locale-ci=? string-locale-ci<? string-locale-ci>?)
 (string? string? . -> . string?))
(def-prims (string-locale-upcase string-locale-downcase)
 (string? . -> . string?))

;; 4.3.5 Additional String Functions
#;[string-append* #;FIXME]
#;[string-join ; FIXME uses, listof
   ((listof string?) . -> . string?)]
(def-prim string-normalize-spaces ; FIXME uses
 (string? . -> . string?))
(def-prim string-replace ; FIXME uses
 (string? (or/c string? regexp?) string? . -> . string?))
#;[string-split ; FIXME uses, listof
   (string? . -> . (listof string?))]
(def-prim string-trim ; FIXME uses
 (string? . -> . string?))
(def-pred non-empty-string?)
[def-prims (string-contains? string-prefix? string-suffix?)
 (string? string? . -> . boolean?)]

;; 4.3.6 Converting Values to Strings.
(def-prims (~a ~v ~s ~e ~.a ~.v ~.s) (any/c . -> . string?)) ; FIXME uses
(def-prim ~r (rational? . -> . string?)) ; FIXME uses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.4 Byte Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 4.4.1 Constructors, Selectors, Mutators
(def-pred bytes?)
(def-prim/todo make-bytes ; FIXME uses
 (exact-nonnegative-integer? byte? . -> . bytes?))
#;[bytes
   (-> bytes)]
(def-prim/todo bytes->immutable-bytes
 (bytes? . -> . (and/c bytes? immutable?)))
(def-pred byte?)
(def-prim/todo bytes-length
 (bytes? . -> . exact-nonnegative-integer?))
(def-prim/todo bytes-ref
 (bytes exact-nonnegative-integer? . -> . byte?))
(def-prim/todo bytes-set!
 ((and/c bytes? (not/c immutable?)) exact-nonnegative-integer? byte? . -> . void?))
(def-prim/todo subbytes ; FIXME uses
 (bytes? exact-nonnegative-integer? . -> . bytes?))
(def-prim/todo bytes-copy
 (bytes? . -> . bytes?))
(def-prim/todo bytes-copy! ; FIXME uses
 ((and/c bytes? (not/c immutable?)) exact-nonnegative-integer? bytes? . -> . void?))
(def-prim/todo bytes-fill!
 ((and/c bytes? (not/c immutable?)) byte? . -> . void?))
#;[bytes-append ; FIXME listof
   (() #:rest (listof bytes?) . ->* . bytes?)]
#;[bytes->list ; FIXME listof
   (bytes? . -> . (listof byte?))]
#;[list->bytes ; FIXME listof
   ((listof byte?) . -> . bytes?)]
(def-prim/todo make-shared-bytes ; FIXME uses
 (exact-nonnegative-integer? byte? . -> . bytes?))
#;[shared-bytes
   (-> bytes)]

;; 4.4.2 Byte String Comparisons
; FIXME varargs
(def-prims (bytes=? bytes<? bytes>?)
 (bytes? bytes? . -> . boolean?))

;; 4.4.3 Bytes to/from Characers, Decoding and Encoding
; FIXME uses
(def-prims (bytes->string/utf-8 bytes->string/locale bytes->string/latin-1)
 (bytes? . -> . string?))
(def-prims (string->bytes/utf-8 string->bytes/locale string->bytes/latin-1)
 (string? . -> . bytes?))
(def-prim/todo string-utf-8-length ; FIXME uses
 (string? . -> . exact-nonnegative-integer?))
(def-prim/todo bytes-utf-8-length ; FIXME uses
 (bytes? . -> . exact-nonnegative-integer?))
(def-prims (bytes-utf-8-ref bytes-utf-8-index) ; FIXME uses
 (bytes? exact-nonnegative-integer? . -> . char?))

;; 4.4.4 Bytes to Bytes Encoding Conversion
(def-prim/todo bytes-open-converter
 (string? string? . -> . (or/c bytes-converter? not)))
(def-prim/todo bytes-close-converter
 (bytes-converter? . -> . void?))
#;[bytes-convert FIXME
                 (bytes-converter? bytes? . -> . any/c)]
#;[bytes-convert-end]
(def-pred bytes-converter?)
(def-prim/todo locale-string-encoding
 (-> any/c))

;; 4.4.5 Additional Byte String Functions
#;[bytes-append*]
#;[bytes-join ; FIXME listof
   ((listof bytes?) bytes? . -> . bytes?)]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.5 Characters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 4.5.1 Characters and Scalar Values

(def-pred char?)
(def-prim char->integer
 (char? . -> . exact-integer?))
(def-prim integer->char ; FIXME range
 (exact-integer? . -> . char?))
(def-prim char-utf-8-length ; FIXME range
 (char? . -> . exact-integer?))

;; 4.5.2 Comparisons
(def-prims (char=? char<? char<=? char>? char>=?
            char-ci=? char-ci<? char-ci<=? char-ci>? char-ci>=?) ; FIXME varargs
 (char? char? . -> . boolean?))

;; 4.5.3 Classifications
(def-prims (char-alphabetic? char-lower-case? char-upper-case? char-title-case?
            char-numeric? char-symbolic? char-punctuation? char-graphic?
            char-whitespace? char-blank? char-iso-control? char-general-category)
 (char? . -> . boolean?))
#;[make-known-char-range-list ; FIXME listof
   (-> (listof (list/c exact-nonnegative-integer?
                       exact-nonnegative-integer?
                       boolean?)))]

;; 4.5.4 Character Conversions
[def-prims (char-upcase char-downcase char-titlecase char-foldcase)
 (char? . -> . char?)]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.6 Symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-pred symbol?)
(def-pred symbol-interned? (symbol?))
(def-pred symbol-unreadable? (symbol?))
(def-prim symbol->string
 (symbol? . -> . string?))
(def-prims (string->symbol string->uninterned-symbol string->unreadable-symbol)
 (string? . -> . symbol?))
(def-prim/todo gensym ; FIXME use
 (-> symbol?))
(def-pred symbol<? (symbol? symbol?)) ; FIXME varargs


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.7 Regular Expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 4.7.3 Constructors
(def-pred regexp?)
(def-pred pregexp?)
(def-pred byte-regexp?)
(def-pred byte-pregexp?)
(def-prim regexp (string? . -> . regexp?))
(def-prim pregexp (string? . -> . pregexp?))
(def-prim byte-regexp (bytes? . -> . regexp?))
(def-prim byte-pregexp (bytes? . -> . pregexp?))
(def-prim/todo regexp-quote ; FIXME uses
 ((or/c string? bytes?) . -> . (or/c string? bytes?))
 #:refinements
 (string? . -> . string?)
 (bytes? . -> . bytes?))
(def-prim/todo regexp-max-lookbehind
 (exact-nonnegative-integer? . -> . (or/c regexp? byte-regexp?)))

;; 4.7.4 Regexp Matching
(def-prim/todo regexp-match ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  any/c))
(def-prim/todo regexp-match* ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  any/c))
(def-prim/todo regexp-try-match ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  any/c))
(def-prim/todo regexp-match-positions ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  any/c))
(def-prim/todo regexp-match-positions* ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  any/c))
(def-prim/todo regexp-match? ; FIXME uses
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  boolean?))
(def-prim/todo regexp-match-exact? ; FIXME uses
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path?)
  . -> .
  boolean?))
#;[regexp-match-peek ; FIXME uses ; FIXME listof
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    (or/c (cons/c bytes? (listof (or/c bytes? not)))))]
#;[regexp-match-peek-positions ; FIXME uses ; FIXME listof
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    (or/c (cons/c (cons/c exact-nonnegative-integer?
                          exact-nonnegative-integer?)
                  (listof (or/c (cons/c exact-nonnegative-integer?
                                        exact-nonnegative-integer?)
                                not)))
          not))]
#;[regexp-match-peek-immediate ; FIXME uses ; FIXME listof
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    (or/c (cons/c bytes? (listof (or/c bytes? not)))
          not))]
#;[regexp-match-peek-positions-immediate ; FIXME uses ; FIXME listof
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    (or/c (cons/c (cons/c exact-nonnegative-integer?
                          exact-nonnegative-integer?)
                  (listof (or/c (cons/c exact-nonnegative-integer?
                                        exact-nonnegative-integer?)
                                not)))
          not))]
#;[regexp-match-peek-positions* ; FIXME uses, precision ; FIXME listof
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    (or/c (listof (cons/c exact-nonnegative-integer?
                          exact-nonnegative-integer?))
          (listof (listof (or/c not (cons/c exact-nonnegative-integer?
                                            exact-nonnegative-integer?))))))]
(def-prim/todo regexp-match/end
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? path? input-port?)
  . -> .
  any/c))
#;[regexp-match-positions/end ; FIXME uses
   ((or/c string? bytes? regexp? byte-regexp?)
    (or/c string? bytes? path? input-port?)
    . -> .
    any/c)]
#;[regexp-match-peek-positions/end
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    any/c)]
#;[regexp-match-peek-positions-immediate/end
   ((or/c string? bytes? regexp? byte-regexp?)
    input-port?
    . -> .
    any/c)]

;; 4.7.5 Regexp Splitting
(def-prim/todo regexp-split ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes? input-port?)
  . -> .
  any/c))

;; 4.7.6 Regexp Substitution
(def-prim/todo regexp-replace ; FIXME uses, precision
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes?)
  (or/c string? bytes? #|TODO more|#)
  . -> .
  any/c))
(def-prim/todo regexp-replace* ; FIXME uses
 ((or/c string? bytes? regexp? byte-regexp?)
  (or/c string? bytes?)
  (or/c string? bytes? #|TODO more|#)
  . -> .
  (or/c string? bytes?)))
#;[regexp-replaces ; FIXME listof
   ((or/c string? bytes?)
    (listof
     (list/c (or/c string? bytes regexp? byte-regexp?)
             (or/c string bytes? #|TODO more|#)))
    . -> .
    (or/c string? bytes?))]
(def-prim/todo regexp-replace-quote
 ((or/c string? bytes?) . -> . (or/c string? bytes?))
 (string? . -> . string?)
 (bytes? . -> . bytes?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.8 Keywords
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred keyword?)
(def-prim keyword->string
 (keyword? . -> . string?))
(def-prim string->keyword
 (string? . -> . keyword?))
(def-pred keyword<? (keyword? keyword?)) ; FIXME varargs


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.9 Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 4.9.1 Constructors and Selectors

(def-pred null?)
(def-alias-internal cons? -cons?)
(def-alias-internal cons -cons)
(def-alias-internal car -car)
(def-alias-internal cdr -cdr)
(def-prim/todo list? (any/c . -> . boolean?))
(def-prim/todo list (() #:rest list? . ->* . list?))
(def-prim/todo list* ; FIXME
  (-> list?))
; [HO] build-list

;; 4.9.2 List Operations
(def-prim length (list? . -> . exact-nonnegative-integer?))
(def-prim/todo list-ref
 (pair? exact-nonnegative-integer? . -> . any/c))
(def-prim/todo list-tail
 (any/c exact-nonnegative-integer? . -> . any/c)
 #:refinements
 (list? exact-nonnegative-integer? . -> . list?))
(def-prim/todo append ; FIXME uses
 (list? list? . -> . list?))
(def-prim/todo reverse
 (list? . -> . list?))

;; 4.9.3 List Iteration
(def-prim/todo map ; FIXME uses
 (procedure? list? . -> . list?))
(def-prims (andmap ormap) ; FIXME uses
 (procedure? list . -> . any/c))
(def-prim/todo for-each ; FIXME uses
 (procedure? list? . -> . void?))
(def-prims (foldl foldr) ; FIXME uses
 (procedure? any/c list? . -> . any/c))

;; 4.9.4 List Filtering
(def-prim/todo filter
 ((any/c . -> . any/c) list? . -> . list?))
(def-prim/todo remove ; FIXME uses
 (any/c list? . -> . list?))
(def-prims (remq remv)
 (any/c list? . -> . list?))
(def-prim/todo remove* ; FIXME uses
 (list? list? . -> . list?))
(def-prims (remq* remv*)
 (list? list? . -> . list?))
(def-prim/todo sort ; FIXME uses
 (list? (any/c any/c . -> . any/c) . -> . list?))

;; 4.9.5 List Searching
(def-prim/todo member ; FIXME uses
 (any/c list? . -> . (or/c list? not)))
(def-prims (memv memq)
 (any/c list? . -> . (or/c list? not)))
(def-prim/todo memf ; TODO why doc only requires `procedure?` and not `arity-includes 1`
 (procedure? list? . -> . (or/c list? not)))
(def-prim/todo findf
 (procedure? list? . -> . any/c))
#;[assoc ; FIXME uses ; FIXME listof
   (any/c (listof pair?) . -> . (or/c pair? not))]
#;[def-prims (assv assq) ; FIXME listof
   (any/c (listof pair?) . -> . (or/c pair? not))]
(def-prim/todo assf ; TODO why doc only requires `procedure?`
 (procedure? list? . -> . (or/c pair? not)))

;; 4.9.6 Pair Acesssor Shorthands
; FIXME these are *opaque* for now. Make them composition of accessors
(def-prims (#:todo caar cdar)
 ((cons/c pair? any/c) . -> . any/c))
(def-prims (#:todo cadr cddr)
 ((cons/c any/c pair?) . -> . any/c))
(def-prim caaar
 ((cons/c (cons/c pair? any/c) any/c) . -> . any/c))
(def-prim caadr
 ((cons/c any/c (cons/c pair? any/c)) . -> . any/c))
(def-prim cadar
 ((cons/c (cons/c any/c pair?) any/c) . -> . any/c))
(def-prim caddr
 ((cons/c any/c (cons/c any/c pair?)) . -> . any/c))
(def-prim cdaar
 ((cons/c (cons/c pair? any/c) any/c) . -> . any/c))
(def-prim cdadr
 ((cons/c any/c (cons/c pair? any/c)) . -> . any/c))
(def-prim cddar
 ((cons/c (cons/c any/c pair?) any/c) . -> . any/c))
(def-prim cdddr
 ((cons/c any/c (cons/c any/c pair?)) . -> . any/c))
; TODO rest of them

;; 4.9.7 Additional List Functions and Synonyms
(def-const empty)
(def-alias pair? cons?)
(def-alias empty? null?)
(def-prim/todo first
 ((cons/c any/c list?) . -> . any/c))
(def-prim/todo rest
 ((cons/c any/c list?) . -> . any/c))
(def-prim/todo second
 ((cons/c any/c (cons/c any/c list?)) . -> . any/c))
(def-prim/todo third
 ((cons/c any/c (cons/c any/c (cons/c any/c list?))) . -> . any/c))
(def-prim/todo fourth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))) . -> . any/c))
(def-prim/todo fifth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))) . -> . any/c))
(def-prim/todo sixth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))) . -> . any/c))
(def-prim/todo seventh
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))) . -> . any/c))
(def-prim/todo eighth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))) . -> . any/c))
(def-prim/todo ninth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))))) . -> . any/c))
(def-prim/todo tenth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))))) . -> . any/c))
(def-prim/todo last
 ((and/c list? (not/c empty?)) . -> . any/c))
(def-prim/todo last-pair
 (pair? . -> . pair?))
(def-prim/todo make-list
 (exact-nonnegative-integer? any/c . -> . list?))
(def-prim/todo list-update ; FIXME range
 (list? exact-nonnegative-integer? (any/c . -> . any/c) . -> . list?))
(def-prim/todo list-set ; FIXME range
 (list? exact-nonnegative-integer? any/c . -> . list?))
(def-prim/todo take ; FIXME range
 (list? exact-nonnegative-integer? . -> . list?))
(def-prim/todo drop
 (any/c exact-nonnegative-integer? . -> . any/c))
#;[split-at ; FIXME
   (any/c exact-nonnegative-integer? . -> . (values list? any/c))]
(def-prim/todo takef
 (any/c procedure? . -> . list?))
(def-prim/todo dropf
 (any/c procedure? . -> . any/c))
(def-prim/todo splitf-at ; FIXME
 (any/c procedure? . -> . (values list? any/c)))
(def-prim/todo take-right
 (any/c exact-nonnegative-integer? . -> . any/c))
(def-prim/todo drop-right
 (any/c exact-nonnegative-integer? . -> . list?))
#;[split-at-right ; FIXME
   (any/c exact-nonnegative-integer? . -> . (values list? any/c))]
(def-prim/todo takef-right
 (any/c procedure? . -> . list?))
(def-prim/todo dropf-right
 (any/c procedure? . -> . any/c))
#;[splitf-at-right ; FIXME uses
   (any/c procedure? . -> . (values list? any/c))]
(def-prim list-prefix? ; FIXME uses
 (list? list? . -> . boolean?))
(def-prim/todo take-common-prefix ; FIXME uses
 (list? list? . -> . list?))
#;[drop-common-prefix ; FIXME uses
   (list? list? . -> . (values list? list?))]
#;[split-common-prefix ; FIXME uses
   (list? list? . -> . (values list? list? list?))]
(def-prim/todo add-between ; FIXME uses
 (list? any/c . -> . list?))
#;[append* ; FIXME uses ; FIXME listof
   ((listof list?) . -> . list?)]
(def-prim/todo flatten
 (any/c . -> . list?))
(def-prim/todo check-duplicates ; FIXME uses
 (list? . -> . any/c)) ; simplified from doc's `(or/c any/c #f)`
(def-prim/todo remove-duplicates ; FIXME uses
 (list? . -> . list?))
(def-prim/todo filter-map ; FIXME uses
 (procedure? list? . -> . list?))
(def-prim/todo count ; FIXME varargs
 (procedure? list? . -> . exact-nonnegative-integer?))
#;[partition
   (procedure? list? . -> . (values list? list?))]
(def-prim/todo range ; FIXME uses
 (real? . -> . list?))
(def-prim/todo append-map ; FIXME varargs
 (procedure? list? . -> . list?))
(def-prim/todo filter-not
 ((any/c . -> . any/c) list? . -> . list?))
(def-prim/todo shuffle
 (list? . -> . list?))
(def-prim/todo permutations
 (list? . -> . list?))
(def-prim/todo in-permutations
 (list? . -> . sequence?))
; [HO] argmin argmax
#;[group-by ; FIXME uses ; FIXME listof
   ((any/c . -> . any/c) list? . -> . (listof list?))]
#;[cartesian-product ; FIXME varargs ; FIXME listof
   (() #:rest (listof list?) . ->* . (listof list?))]
(def-prim/todo remf
 (procedure? list? . -> . list?))
(def-prim/todo remf*
 (procedure? list? . -> . list?))

;; 4.9.8 Immutable Cyclic Data
(def-prim/todo make-reader-graph
 (any/c . -> . any/c))
(def-pred/todo placeholder?)
(def-prim/todo make-placeholder
 (any/c . -> . placeholder?))
(def-prim/todo placeholder-set!
 (placeholder? any/c . -> . void?))
(def-prim/todo placeholder-get
 (placeholder? . -> . any/c))
(def-pred/todo hash-placeholder?)
#;[def-prims (make-hash-placeholder make-hasheq-placeholder make-hasheqv-placeholder) ; FIXME listof
   ((listof pair?) . -> . hash-placeholder?)]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.10 Mutable Pairs and Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TODO


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Vectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred vector?) ; FIXME alias for internal `vector?`
(def-prim/todo make-vector
 (exact-nonnegative-integer? any/c . -> . (and/c vector? (not/c immutable?))))
(def-prim/todo vector
 (() #:rest list? . ->* . (and/c vector? (not/c immutable?))))
(def-prim/todo vector-immutable
 (() #:rest list? . ->* . (and/c vector? immutable?)))
(def-prim/todo vector-length
 (vector? . -> . exact-nonnegative-integer?))
(def-prim/todo vector-ref
 (vector? exact-nonnegative-integer? . -> . any/c))
(def-prim/todo vector-set!
 ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?))
(def-prim/todo vector->list
 (vector? . -> . list?))
(def-prim/todo list->vector
 (list? . -> . vector?))
(def-prim/todo vector->immutable-vector
 (vector? . -> . (and/c vector? immutable?)))
(def-prim/todo vector-fill!
 ((and/c vector? (not/c immutable?)) any/c . -> . void?))
(def-prim/todo vector-copy! ; FIXME uses
 ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? . -> . void?))
#;[vector->values ; FIXME uses, var-values, `any` instead of `any/c`
   (vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . any)]
(def-prim/todo build-vector
 (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . any/c)
                             . -> . (and/c vector? (not/c immutable?))))

;; 4.11.1 Additional Vector Functions
(def-prim/todo vector-set*! ; FIXME uses
 ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?))
(def-prim/todo vector-map ; FIXME uses
 (procedure? vector? . -> . vector?))
(def-prim/todo vector-map! ; FIXME uses
 (procedure? (and/c vector? (not/c immutable?)) . -> . vector?))
#;[vector-append ; FIXME listof
   (() #:rest (listof vector?) . ->* . vector?)]
(def-prim/todo vector-take
 (vector? exact-nonnegative-integer? . -> . vector?))
(def-prim/todo vector-take-right
 (vector? exact-nonnegative-integer? . -> . vector?))
(def-prim/todo vector-drop
 (vector? exact-nonnegative-integer? . -> . vector?))
(def-prim/todo vector-drop-right
 (vector? exact-nonnegative-integer? . -> . vector?))
(def-prim/todo vector-split-at
 (vector? exact-nonnegative-integer? . -> . (values vector? vector?)))
(def-prim/todo vector-split-at-right
 (vector? exact-nonnegative-integer? . -> . (values vector? vector?)))
(def-prim/todo vector-copy ; FIXME uses
 (vector? . -> . vector?))
; [HO] vector-filter vector-filter-not
(def-prim/todo vector-count ; FIXME varargs
 (procedure? vector? . -> . exact-nonnegative-integer?))
; [HO] vector-argmin vector-argmax
(def-prims (vector-member vector-memv vector-memq)
 (any/c vector? . -> . (or/c exact-nonnegative-integer? not)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.12 Boxes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-alias-internal box? -box?)
(def-alias-internal box -box)
(def-alias-internal unbox -unbox)
(def-alias-internal set-box! -set-box!)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.13 Hash Tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred hash?)
(def-prims (hash-equal? hash-eqv? hash-eq? hash-weak?)
 (hash? . -> . boolean?))
(def-prim/todo hash ; FIXME uses
 (any/c any/c . -> . (and/c hash? hash-equal? immutable?)))
(def-prim/todo hasheq ; FIXME uses
 (any/c any/c . -> . (and/c hash? hash-eq? immutable?)))
(def-prim/todo hasheqv
 (any/c any/c . -> . (and/c hash? hash-eqv? immutable?)))
#;[make-hash ; FIXME uses ; FIXME listof
   ((listof pair?) . -> . (and/c hash? hash-equal?))]
#;[make-hasheqv ; FIXME uses ; FIXME listof
   ((listof pair?) . -> . (and/c hash? hash-eqv?))]
#;[make-hasheq ; FIXME uses ; FIXME listof
   ((listof pair?) . -> . (and/c hash? hash-eq?))]
#;[make-weak-hash ; FIXME uses ; FIXME listof
   ((listof pair?) . -> . (and/c hash? hash-equal? hash-weak?))]
#;[make-weak-hasheqv ; FIXME uses ; FIXME listof
   ((listof pair?) . -> . (and/c hash? hash-eqv? hash-weak?))]
#;[make-weak-hasheq ; FIXME uses ; FIXME listof
   ((listof pair?) . -> . (and/c hash? hash-eq? hash-weak?))]
(def-prim/todo hash-set!
 ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?))
(def-prim/todo hash-set*! ; FIXME uses
 ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?))
(def-prim/todo hash-set ; FIXME refine with `eq?` and `eqv?`
 ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?)))
(def-prim/todo hash-set* ; FIXME refine with `eq?` and `eqv?`
 ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?)))
(def-prim/todo hash-ref ; FIXME uses
 (hash? any/c . -> . any/c))
(def-prim/todo hash-ref! ; FIXME precision
 (hash? any/c any/c . -> . any/c))
(def-prim/todo hash-has-key?
 (hash? any/c . -> . boolean?))
(def-prim/todo hash-update! ; FIXME uses
 ((and/c hash? (not/c immutable?)) any/c (any/c . -> . any/c) . -> . void?))
(def-prim/todo hash-update
 ((and/c hash? immutable?) any/c (any/c . -> . any/c) . -> . (and/c hash? immutable?)))
(def-prim/todo hash-remove!
 ((and/c hash? (not/c immutable?)) any/c . -> . void?))
(def-prim/todo hash-remove
 ((and/c hash? immutable?) any/c . -> . (and/c hash? immutable?)))
(def-prim/todo hash-clear!
 ((and/c hash? (not/c immutable?)) . -> . void?))
(def-prim/todo hash-clear
 ((and/c hash? immutable?) . -> . (and/c hash? immutable?)))
(def-prim/todo hash-copy-clear
 (hash? . -> . hash?))
#;[hash-map ; FIXME uses ; FIXME listof
   (hash? (any/c any/c . -> . any/c) . -> . (listof any/c))]
#;[hash-keys ; FIXME listof
   (hash? . -> . (listof any/c))]
#;[hash-values ; FIXME listof
   (hash? . -> . (listof any/c))]
#;[hash->list ; simplified from doc's `(cons/c any/c any/c)` ; FIXME listof
   (hash? . -> . (listof pair?))]
(def-prim/todo hash-for-each ; FIXME uses
 (hash? (any/c any/c . -> . any) . -> . void?))
(def-prim/todo hash-count
 (hash? . -> . exact-nonnegative-integer?))
(def-prim/todo hash-empty?
 (hash? . -> . boolean?))
(def-prim/todo hash-iterate-first
 (hash? . -> . (or/c exact-nonnegative-integer? not)))
(def-prim/todo hash-iterate-next
 (hash? exact-nonnegative-integer? . -> . (or/c exact-nonnegative-integer? not)))
(def-prims (hash-iterate-key hash-iterate-value)
 (hash? exact-nonnegative-integer? . -> . any/c))
(def-prim/todo hash-copy
 (hash? . -> . (and/c hash? (not/c immutable?))))
[def-prims (eq-hash-code eqv-hash-code equal-hash-code equal-secondary-hash-code)
 (any/c . -> . fixnum?)]

;; 4.13.1 Additional Hash Table Functions
; FIXME wtf is `hash-can-functional-set?`
;[hash-union ]
;[hash-union!]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.14 Sequences and Streams
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;;;;; 4.14.1 Sequences

;; 4.14.1.1 Predicate and Constructors
(def-pred sequence?)
(def-prim/todo in-range ; FIXME uses
 (real? . -> . stream?))
(def-prim/todo in-naturals ; FIXME uses
 (exact-nonnegative-integer? . -> . stream?))
(def-prim/todo in-list
 (list? . -> . stream?))
#;[in-mlist ; FIXME don't know about `mlist?`
   (mlist? . -> . stream?)]
(def-prim/todo in-vector ; FIXME uses
 (vector? . -> . sequence?))
(def-prim/todo in-string ; FIXME uses
 (string? . -> . sequence?))
(def-prim/todo in-bytes ; FIXME uses
 (bytes? . -> . sequence?))
(def-prim/todo in-port ; FIXME uses
 ((input-port? . -> . any/c) input-port? . -> . sequence?))
(def-prim/todo in-input-port-bytes
 (input-port? . -> . sequence?))
(def-prim/todo in-input-port-chars
 (input-port? . -> . sequence?))
(def-prim/todo in-lines ; FIXME uses
 (input-port? (one-of/c 'linefeed 'return 'return-linefeed 'any 'any-one)
              . -> . sequence?))
(def-prim/todo in-bytes-lines ; FIXME uses
 (input-port? (one-of/c 'linefeed 'return 'return-linefeed 'any 'any-one)
              . -> . sequence?))
(def-prim/todo in-hash
 (hash? . -> . sequence?))
(def-prims (in-hash-keys in-hash-values)
 (hash? . -> . sequence?))
(def-prim/todo in-hash-pairs
 (hash? . -> . sequence?))
(def-prim/todo in-directory ; FIXME uses
 ((or/c path-string? not) . -> . sequence?))
(def-prim/todo in-producer ; FIXME uses
 (procedure? . -> . sequence?))
(def-prim/todo in-value
 (any/c . -> . sequence?))
(def-prim/todo in-indexed
 (sequence? . -> . sequence?))
#;[in-sequences ; FIXME listof
   (() #:rest (listof sequence?) . ->* . sequence?)]
#;[in-cycle ; FIXME listof
   (() #:rest (listof sequence?) . ->* . sequence?)]
#;[in-parallel ; FIXME listof
   (() #:rest (listof sequence?) . ->* . sequence?)]
(def-prim/todo in-values-sequence
 (sequence? . -> . sequence?))
(def-prim/todo in-values*-sequence
 (sequence? . -> . sequence?))
; [HO] stop-before stop-after
(def-prim/todo make-do-sequence
 ((-> (values (any/c . -> . any/c)
              (any/c . -> . any/c)
              any/c
              (or/c (any/c . -> . any/c) not)
              ; FIXME optional arg
              #;(or/c (() () #:rest list? . ->* . any/c) not)
              #;(or/c ((any/c) () #:rest list? . ->* . any/c) not)))
  . -> . sequence?))
(def-opq prop:sequence struct-type-property?)

;; 4.14.1.2 Sequence Conversion
(def-prim/todo sequence->stream
 (sequence? . -> . stream?))
(def-prim/todo sequence-generate
 (sequence? . -> . (values (-> boolean?) (-> any))))
(def-prim/todo sequence-generate*
 (sequence? . -> . (values (or/c list? not)
                           (-> (values (or/c list? not) procedure?)))))

;; 4.14.1.3 Additional Sequence Operations
(def-prim/todo empty-sequence sequence?)
(def-prim/todo sequence->list
 (sequence? . -> . list?))
(def-prim/todo sequence-length
 (sequence? . -> . exact-nonnegative-integer?))
(def-prim/todo sequence-ref
 (sequence? exact-nonnegative-integer? . -> . any))
(def-prim/todo sequence-tail
 (sequence? exact-nonnegative-integer? . -> . sequence?))
#;[sequence-append ; FIXME listof
   (() #:rest (listof sequence?) . ->* . sequence?)]
(def-prim/todo sequence-map
 ((any/c . -> . any/c) sequence? . -> . sequence?))
; [HO] sequence-andmap sequence-ormap
(def-prim/todo sequence-for-each ; FIXME generalize 1st arg to multi args
 ((any/c . -> . any) sequence? . -> . void?))
(def-prim/todo sequence-fold ; FIXME generalize 1st arg
 ((any/c any/c . -> . any/c) any/c sequence? . -> . any/c))
(def-prim/todo sequence-count ; FIXME precise arity for 1st arg
 (procedure? sequence? . -> . exact-nonnegative-integer?))
(def-prim/todo sequence-filter ; FIXME generalize 1st arg to multi args
 ((any/c . -> . boolean?) sequence? . -> . sequence?))
(def-prim/todo sequence-add-between
 (sequence? any/c . -> . sequence?))
#;[sequence/c ; FIXME uses, `contract?`
   (any/c . -> . any/c)]

; 4.14.1.3.1 Additional Sequence Constructors
#;[in-syntax
   (syntax? . -> . sequence?)]
(def-prim/todo in-slice
 (exact-positive-integer? sequence? . -> . sequence?))

     ;;;;; 4.14.2 Streams
(def-pred/todo stream?)
(def-pred stream-empty? (stream?))
(def-prim/todo stream-first
 ((and/c stream? (not/c stream-empty?)) . -> . any))
(def-prim/todo stream-rest
 ((and/c stream? (not/c stream-empty?)) . -> . stream?))
(def-prim/todo in-stream
 (stream? . -> . sequence?))
(def-prim/todo empty-stream stream?)
(def-prim/todo stream->list
 (stream? . -> . list?))
(def-prim/todo stream-length
 (stream? . -> . exact-nonnegative-integer?))
(def-prim/todo stream-ref
 (stream? exact-nonnegative-integer? . -> . any))
(def-prim/todo stream-tail
 (stream? exact-nonnegative-integer? . -> . stream?))
#;[stream-append ; FIXME listof
   (() #:rest (listof stream?) . ->* . stream?)]
(def-prim/todo stream-map
 (procedure? stream? . -> . stream?))
; [HO] stream-andmap stream-ormap
(def-prim/todo stream-for-each ; FIXME varargs on 1st
 ((any/c . -> . any) stream? . -> . void?))
(def-prim/todo stream-fold ; FIXME varargs on 1st
 ((any/c any/c . -> . any) any/c stream? . -> . any/c))
(def-prim/todo stream-count ; FIXME varargs on 1st
 (procedure? stream? . -> . exact-nonnegative-integer?))
(def-prim/todo stream-filter ; FIXME varargs on 1st
 ((any/c . -> . boolean?) stream? . -> . stream?))
(def-prim/todo stream-add-between
 (stream? any/c . -> . stream?))
(def-opq prop:stream struct-type-property?)
(def-prim/todo stream/c
 (contract? . -> . contract?))

     ;;;;; 4.14.3 Generators
(def-pred/todo generator?)
#;[yield ; FIXME uses
   (-> any)]
(def-prim/todo generator-state
 (generator? . -> . symbol?))
(def-prim/todo sequence->generator
 (sequence? . -> . (-> any)))
(def-prim/todo sequence->repeated-generator
 (sequence? . -> . (-> any)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.15 Dictionaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;; 4.15.1 Dictionary Predicates and Contracts
(def-pred/todo dict?)
(def-prim/todo dict-implements? ; FIXME varargs
 (dict? symbol? . -> . boolean?))
#;[dict-implements/c ; FIXME varargs, contracts
   (symbol? . -> . flat-contract?)]
[def-pred dict-mutable? (dict?)]
[def-pred dict-can-remove-keys? (dict?)]
[def-pred dict-can-functional-set? (dict?)]

     ;;;;; 4.15.2 Generic Dictionary Interface
(def-opq prop:dict struct-type-property?)

;; 4.15.2.1 Primitive Dictionary Methods
(def-prim/todo dict-ref ; FIXME use
 (dict? any/c . -> . any))
(def-prim/todo dict-set!
 ((and/c dict? (not/c immutable?)) any/c any/c . -> . void?))
(def-prim/todo dict-set
 ((and/c dict? immutable?) any/c any/c . -> . (and/c dict? immutable?)))
(def-prim/todo dict-remove!
 ((and/c dict? (not/c immutable?)) any/c . -> . void?))
(def-prim/todo dict-remove
 ((and/c dict? immutable?) any/c . -> . (and/c dict? immutable?)))
(def-prim/todo dict-iterate-first
 (dict? . -> . any/c))
(def-prim/todo dict-iterate-next
 (dict? any/c . -> . any/c))
(def-prim/todo dict-iterate-key
 (dict? any/c . -> . any))
(def-prim/todo dict-iterate-value
 (dict? any/c . -> . any))

;; 4.15.2.2 Derived Dictionary Methods
[def-pred dict-has-key? (dict? any/c)]
(def-prim/todo dict-set*! ; FIXME use
 ((and/c dict? (not/c immutable?)) any/c any/c . -> . void?))
(def-prim/todo dict-set* ; FIXME use
 ((and/c dict? immutable?) any/c any/c . -> . (and/c dict? immutable?)))
(def-prim/todo dict-ref!
 (dict? any/c any/c . -> . any))
(def-prim/todo dict-update! ; FIXME use
 ((and/c dict? (not/c immutable?)) any/c (any/c . -> . any/c) . -> . void?))
(def-prim/todo dict-update
 ((and/c dict? immutable?) any/c (any/c . -> . any/c) . -> . (and/c dict? immutable?)))
#;[dict-map ; FIXME listof
   (dict? (any/c any/c . -> . any/c) . -> . (listof any/c))]
(def-prim/todo dict-for-each
 (dict? (any/c any/c . -> . any) . -> . void?))
(def-pred dict-empty? (dict?))
(def-prim/todo dict-count
 (dict? . -> . exact-nonnegative-integer?))
(def-prim/todo dict-copy
 (dict? . -> . dict?))
(def-prim/todo dict-clear
 (dict? . -> . dict?))
(def-prim/todo dict-clear!
 (dict? . -> . void?))
[def-prims (dict-keys dict-values)
 (dict? . -> . list?)]
#;[dict->list ; TODO more precise than doc. Confirm. ; FIXME listof
   (dict? . -> . (listof pair?))]

;;;;; 4.15.3 Dictionary Sequences
(def-prim/todo in-dict
 (dict? . -> . sequence?))
(def-prims (in-dict-keys in-dict-values)
 (dict? . -> . sequence?))
(def-prim/todo in-dict-pairs
 (dict? . -> . sequence?))

;;;;; 4.15.4 Contracted Dictionaries
(def-opq prop:dict/contract struct-type-property?)
#;[def-prims (dict-key-contract dict-value-contract dict-iter-contract) ; FIXME contract?
   (dict? . -> . contract?)]

     ;;;;; 4.15.5 Custom Hash Tables
;[make-custom-hash-types ; FIXME uses, ->*
; ((or/c (any/c any/c . -> . any/c)
;        (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
;  . -> . (values (any/c . -> . boolean?)
;                 (any/c . -> . boolean?)
;                 (any/c . -> . boolean?)
;                 (any/c . -> . boolean?)
;                 (->* [] [dict?] dict?)
;                 (->* [] [dict?] dict?)
;                 (->* [] [dict?] dict?)))]
[def-prims (#:todo make-custom-hash make-weak-custom-hash make-immutable-custom-hash) ; FIXME uses
 ((or/c (any/c any/c . -> . any/c)
        (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
  . -> . dict?)]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.16 Sets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;; Hash Sets
(def-preds (set-equal? set-eqv? set-eq? set? #:todo set-mutable? set-weak?))
(def-prim/todo set
 (() #:rest list? . ->* . (and/c generic-set? set-equal? set?)))
(def-prim/todo seteqv
 (() #:rest list? . ->* . (and/c generic-set? set-eqv? set?)))
(def-prim/todo seteq
 (() #:rest list? . ->* . (and/c generic-set? set-eq? set?)))
(def-prim/todo mutable-set
 (() #:rest list? . ->* . (and/c generic-set? set-equal? set-mutable?)))
(def-prim/todo mutable-seteqv
 (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-mutable?)))
(def-prim/todo mutable-seteq
 (() #:rest list? . ->* . (and/c generic-set? set-eq? set-mutable?)))
(def-prim/todo weak-set
 (() #:rest list? . ->* . (and/c generic-set? set-equal? set-weak?)))
(def-prim/todo weak-seteqv
 (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-weak?)))
(def-prim/todo weak-seteq
 (() #:rest list? . ->* . (and/c generic-set? set-eq? set-weak?)))
(def-prim/todo list->set
 (list? . -> . (and/c generic-set? set-equal? set?)))
(def-prim/todo list->seteqv
 (list? . -> . (and/c generic-set? set-eqv? set?)))
(def-prim/todo list->seteq
 (list? . -> . (and/c generic-set? set-eq? set?)))
(def-prim/todo list->mutable-set
 (list? . -> . (and/c generic-set? set-equal? set-mutable?)))
(def-prim/todo list->mutable-seteqv
 (list? . -> . (and/c generic-set? set-eqv? set-mutable?)))
(def-prim/todo list->mutable-seteq
 (list? . -> . (and/c generic-set? set-eq? set-mutable?)))
(def-prim/todo list->weak-set
 (list? . -> . (and/c generic-set? set-equal? set-weak?)))
(def-prim/todo list->weak-seteqv
 (list? . -> . (and/c generic-set? set-eqv? set-weak?)))
(def-prim/todo list->weak-seteq
 (list? . -> . (and/c generic-set? set-eq? set-weak?)))

;;;;; 4.16.2 Set Predicates and Contracts
(def-pred generic-set?)
#;[set-implements ; FIXME listof
   ((generic-set?) #:rest (listof symbol?) . ->* . boolean?)]
#;[set-implements/c ; FIXME varargs, contract?
   (symbol? . -> . flat-contract?)]
#;[set/c ; FIXME uses, contract?
   (chaperone-contract? . -> . contract?)]

;;;;; 4.16.3 Generic Set Interface

;; 4.16.3.1 Set Methods
[def-pred set-member? (generic-set? any/c)]
[def-prims (set-add set-remove)
 ((and/c generic-set? (not/c set-mutable?)) any/c . -> . generic-set?)]
[def-prims (set-add! set-remove!)
 ((and/c generic-set? set-mutable?) any/c . -> . void?)]
[def-pred set-empty? (generic-set?)]
(def-prim/todo set-count
 (generic-set? . -> . exact-nonnegative-integer?))
(def-prim/todo set-first
 ((and/c generic-set? (not/c set-empty?)) . -> . any/c))
(def-prim/todo set-rest ; TODO probably refine with (im)mutable? and other modifiers
 ((and/c generic-set? (not/c set-empty?)) . -> . generic-set?))
(def-prim/todo set->stream
 (generic-set? . -> . stream?))
(def-prim/todo set-copy
 (generic-set? . -> . generic-set?))
(def-prim/todo set-copy-clear
 (generic-set? . -> . (and/c generic-set? set-empty?)))
(def-prim/todo set-clear
 ((and/c generic-set? (not/c set-mutable?)) . -> . (and/c generic-set? set-empty?)))
(def-prim/todo set-clear!
 ((and/c generic-set? set-mutable?) . -> . void?))
;; FIXME listof
#|
(def-prim/todo set-union ; FIXME enforce sets of the same type
   ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
(def-prim/todo set-union! ; FIXME enforce sets of the same type
 ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
(def-prim/todo set-intersect
 ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
(def-prim/todo set-intersect!
 ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
(def-prim/todo set-subtract
 ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
(def-prim/todo set-subtract!
 ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
(def-prim/todo set-symmetric-difference
 ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
(def-prim/todo set-symmetric-difference!
 ((generic-set?) #:rest (listof generic-set?) . ->* . void?))|#
(def-prims (set=? subset? proper-subset?) ; FIXME enforce same `set` type
 (generic-set? generic-set? . -> . boolean?))
(def-prim/todo set->list
 (generic-set? . -> . list?))
#;[set-map ; FIXME listof
   (generic-set? (any/c . -> . any/c) . -> . (listof any/c))]
(def-prim/todo set-for-each
 (generic-set? (any/c . -> . any) . -> . void?))
(def-prim/todo in-set
 (generic-set? . -> . sequence?))

;;;;; 4.16.4 Custom Hash Sets
#;[make-custom-set-types ; FIXME uses
   ((or/c (any/c any/c . -> . any/c)
          (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
    . -> .
    (values (any/c . -> . boolean?)
            (any/c . -> . boolean?)
            (any/c . -> . boolean?)
            (any/c . -> . boolean?)
            ([] [stream?] . ->* . generic-set?)
            ([] [stream?] . ->* . generic-set?)
            ([] [stream?] . ->* . generic-set?)))]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.17 Procedures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred procedure?)
#;[apply ; FIXME uses. This probably should be treated specially for precision ; FIXME listof
   (procedure? (listof any/c) . -> . any)]
(def-prim/todo compose ; FIXME uses
 ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any)))
(def-prim/todo compose1 ; FIXME uses
 ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any)))
(def-prim/todo procedure-rename
 (procedure? symbol? . -> . procedure?))
(def-prim/todo procedure->method
 (procedure? . -> . procedure?))
(def-pred procedure-closure-contents-eq? (procedure? procedure?))

;; 4.17.1 Keywords and Arity
;[keyword-apply #|FIXME uses|#]
(def-prim/todo procedure-arity
 (procedure? . -> . normalized-arity?))
(def-pred procedure-arity?)
{def-pred procedure-arity-includes? (procedure? exact-nonnegative-integer?)} ; FIXME uses
(def-prim/todo procedure-reduce-arity
 (procedure? procedure-arity? . -> . procedure?))
#;[procedure-keywords ; FIXME listof
   (procedure? . -> . (values (listof keyword?) (or/c (listof keyword?) not)))]
#;[make-keyword-procedure ; FIXME uses
   ((((listof keyword?) list?) () #:rest list? . ->* . any) . -> . procedure?)]
#;[procedure-reduce-keyword-arity ; FIXME listof
   (procedure? procedure-arity? (listof keyword?) (or/c (listof keyword?) not)
               . -> . procedure?)]
(def-pred arity-at-least?)
(def-prim/todo arity-at-least (exact-nonnegative-integer? . -> . arity-at-least?))
(def-prim/todo arity-at-least-value (arity-at-least? . -> . exact-nonnegative-integer?))
(def-alias make-arity-at-least arity-at-least)
(def-opq prop:procedure struct-type-property?)
[def-pred procedure-struct-type? (struct-type?)]
(def-prim/todo procedure-extract-target
 (procedure? . -> . (or/c procedure? not)))
(def-opq prop:arity-string struct-type-property?)
(def-opq prop:checked-procedure struct-type-property?)
(def-prim/todo checked-procedure-check-and-extract
 (struct-type? any/c (any/c any/c any/c . -> . any/c) any/c any/c . -> . any/c))

;; 4.17.2 Reflecting on Primitives
(def-pred primitive?)
(def-pred primitive-closure?)
(def-prim/todo primitive-result-arity
 (primitive? . -> . procedure-arity?))

;; 4.17.3 Additional Higher-Order Functions
(def-prim/todo identity (any/c . -> . any/c))
(def-prim/todo const (any . -> . procedure?))
(def-prim/todo negate (procedure? . -> . procedure?))
;[curry ] FIXME
;[curryr] FIXME
(def-pred/todo normalized-arity?)
(def-prim/todo normalize-arity ; FIXME dependency
 (procedure-arity? . -> . normalized-arity?))
(def-pred arity=? (procedure-arity? procedure-arity?))
(def-pred arity-includes? (procedure-arity? procedure-arity?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.18 Void
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred void?)
(def-prim/todo void (() #:rest list? . ->* . void?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.19 Undefined
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-const undefined)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.6 Structure Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-pred struct-type?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.1 Data-structure Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-prim/todo flat-named-contract ; FIXME uses
 (any/c flat-contract? . -> . flat-contract?))
(def-prim/todo any/c (any/c . -> . (not/c not)))
(def-prim/todo none/c (any/c . -> . not))
(def-prim/todo  or/c (contract? contract? . -> . contract?)) ; FIXME uses
(def-prim/todo and/c (contract? contract? . -> . contract?)) ; FIXME uses
(def-prim/todo not/c (flat-contract? . -> . flat-contract?))
(def-prim/todo =/c  (real? . -> . flat-contract?))
(def-prim/todo </c  (real? . -> . flat-contract?))
(def-prim/todo >/c  (real? . -> . flat-contract?))
(def-prim/todo <=/c (real? . -> . flat-contract?))
(def-prim/todo >=/c (real? . -> . flat-contract?))
(def-prim/todo between/c (real? real? . -> . flat-contract?))
[def-alias real-in between/c]
(def-prim/todo integer-in (exact-integer? exact-integer? . -> . flat-contract?))
(def-prim/todo char-in (char? char? . -> . flat-contract?))
(def-prim/todo def-alias natural-number/c exact-nonnegative-integer?)
(def-prim/todo string-len/c (real? . -> . flat-contract?))
(def-alias false/c not)
(def-pred printable/c)
#;[one-of/c
   (() #:rest (listof flat-contract?) . ->* . contract?)]
#;[symbols
   (() #:rest (listof symbol?) . ->* . flat-contract?)]
(def-prim/todo vectorof ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo vector-immutableof (contract? . -> . contract?))
(def-prim/todo vector/c ; FIXME uses
 (() #:rest (listof contract?) . ->* . contract?))
#;[vector-immutable/c
   (() #:rest (listof contract?) . ->* . contract?)]
(def-prim/todo box/c ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo box-immutable/c (contract? . -> . contract?))
(def-prim/todo listof (contract? . -> . list-contract?))
(def-prim/todo non-empty-listof (contract? . -> . list-contract?))
(def-prim/todo list*of (contract? . -> . contract?))
(def-prim/todo cons/c (contract? contract? . -> . contract?))
#;[list/c
   (() #:rest (listof contract?) . ->* . list-contract?)]
(def-prim/todo syntax/c (flat-contract? . -> . flat-contract?))
(def-prim/todo parameter/c ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo procedure-arity-includes/c
 (exact-nonnegative-integer? . -> . flat-contract?))
(def-prim/todo hash/c ; FIXME uses
 (chaperone-contract? contract? . -> . contract?))
(def-prim/todo channel/c (contract? . -> . contract?))
(def-prim/todo continuation-mark-key/c (contract? . -> . contract?))
;;[evt/c (() #:rest (listof chaperone-contract?) . ->* . chaperone-contract?)]
(def-prim/todo promise/c (contract? . -> . contract?))
(def-prim/todo flat-contract ((any/c . -> . any/c) . -> . flat-contract?))
(def-prim/todo flat-contract-predicate (flat-contract? . -> . (any/c . -> . any/c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.2 Function Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-opq predicate/c contract?)
(def-opq the-unsupplied-arg unsupplied-arg?)
(def-pred unsupplied-arg?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TODO
(def-prim contract-first-order-passes?
 (contract? any/c . -> . boolean?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred contract?)
(def-pred chaperone-contract?)
(def-pred impersonator-contract?)
(def-pred flat-contract?)
(def-pred list-contract?)
(def-prim/todo contract-name (contract? . -> . any/c))
(def-prim/todo value-contract (has-contract? . -> . (or/c contract? not)))
[def-pred has-contract?]
(def-prim/todo value-blame (has-blame? . -> . (or/c blame? not)))
[def-pred has-blame?]
(def-prim/todo contract-projection (contract? . -> . (blame? . -> . (any/c . -> . any/c))))
(def-prim/todo make-none/c (any/c . -> . contract?))
(def-opq contract-continuation-mark-key continuation-mark-key?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.1 Multiple Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim/custom (values ⟪ℋ⟫ ℓ l Σ Γ Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  {set (-ΓA Γ (-W Vs (apply -?@ 'values ss)))})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.4 Continuations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim/todo call-with-current-continuation ((any/c . -> . any/c) . -> . any/c)) ; FIXME


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.1 Ports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 13.1.2 Managing Ports
(def-prim input-port? (any/c . -> . boolean?))
(def-prim output-port? (any/c . -> . boolean?))
(def-prim port? (any/c . -> . boolean?))
(def-prim eof-object? (any/c . -> . boolean?))
(def-prim current-input-port  (-> input-port?))
(def-prim current-output-port (-> output-port?))
(def-prim current-error-port (-> output-port?))

;; 13.1.3 Port Buffers and Positions
(def-prim flush-output (-> void?)) ; FIXME uses

;; 13.1.5 File Ports
; [HO] call-with-input-file call-with-output-file


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.2 Byte and String Input
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim read-char (input-port? . -> . (or/c char? eof-object?))) ; FIXME uses
(def-prim peek-char (input-port? . -> . (or/c char? eof-object?))) ; FIXME uses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.3 Byte and String Output
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim write-char (char? output-port? . -> . void?)) ; FIXME uses
(def-prim newline (output-port? . -> . void?)) ; FIXME uses


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.5 Writing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim write (any/c . -> . void?)) ; FIXME uses
(def-prim display (any/c output-port? . -> . void?)) ; FIXME uses


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.1 Paths
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 15.1.1 Manipulating Paths
(def-pred path-string?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.2 Filesystem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 15.2.2 Files
(def-prim file-exists? (path-string? . -> . boolean?))
(def-prim delete-file (path-string? . -> . void?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 15.7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

{def-prim getenv (string? . -> . (or/c string? not))}
{def-prim putenv (string? string? . -> . boolean?)}

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 17.2 Unsafe Data Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
[def-alias unsafe-car car]
[def-alias unsafe-cdr cdr]
[def-alias unsafe-vector-length vector-length]
[def-alias unsafe-vector-ref vector-ref]
[def-alias unsafe-vector-set! vector-set!]
(def-prim/todo unsafe-struct-ref (any/c exact-nonnegative-integer? . -> . any/c))
(def-prim/todo unsafe-struct-set! (any/c exact-nonnegative-integer? any/c . -> . any/c))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; FROM THE MATH LIBRARY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 1.2 Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
[def-pred float-complex?]

