#lang typed/racket/base

(provide (all-defined-out))

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
         "../utils/set.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "def-prim-runtime.rkt"
         "def-prim.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.1 Booleans and Equality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-pred boolean?)
(def-pred not)

(def-preds (equal? eqv? eq?) (any/c any/c))
; [HO] equal?/recur
(def-pred immutable?)
(def-opq prop:equal+hash any/c)

(def-const true)
(def-const false)
(def-pred symbol=? (symbol? symbol?))
(def-pred boolean=? (boolean? boolean?))
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
(def-prim +
  (() #:rest (listof number?)  . ->* . number?)
  #:refinements
  (() #:rest (listof exact-positive-integer?) . ->* . exact-positive-integer?)
  (() #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
  (() #:rest (listof exact-integer?) . ->* . exact-integer?)
  (() #:rest (listof integer?) . ->* . integer?)
  (() #:rest (listof real?) . ->* . real?)
  (() #:rest (listof (not/c negative?)) . ->* . (not/c negative?))
  (() #:rest (listof (not/c positive?)) . ->* . (not/c positive?)))
(def-prim - (number? number? . -> . number?)
  ; FIXME var-args and precise refinement for first case
  #:refinements
  (exact-positive-integer? (=/c 1) . -> . exact-nonnegative-integer?)
  (exact-integer? exact-integer? . -> . exact-integer?)
  (integer? integer? . -> . integer?)
  (real? real? . -> . real?))
#;(def-prim -
 ((number?) #:rest (listof number?) . ->* . number?)
 #:refinements
 ((exact-integer?) #:rest (listof exact-integer?) . ->* . exact-integer?)
 ((integer?) #:rest (listof integer?) . ->* . integer?)
 ((real?) #:rest (listof real?) . ->* . real?))
(def-prim *
 (() #:rest (listof number?) . ->* . number?)
 #:refinements
 (() #:rest (listof exact-nonnegative-integer?) . ->* . exact-nonnegative-integer?)
 (() #:rest (listof exact-integer?) . ->* . exact-integer?)
 (() #:rest (listof integer?) . ->* . integer?)
 (() #:rest (listof real?) . ->* . real?))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.3 Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 4.3.1 Constructors, Selectors, Mutators
(def-pred string?)
(def-prim make-string ; FIXME all uses
 (exact-nonnegative-integer? char? . -> . (and/c string? (not/c immutable?))))
(def-prim/custom (string ⟪ℋ⟫ ℓ Σ Γ Ws) ; FIXME uses, domain check
  (define σ (-Σ-σ Σ))
  (define sₐ (apply -?@ 'string (map -W¹-s Ws)))
  (define p
    (cond [(for/and : Boolean ([W Ws])
             (match-define (-W¹ V s) W)
             (⊢?/quick '✗ σ Γ 'equal? W -null-char.W¹))
           'path-string?]
          [else 'string?]))
  {set (-ΓA Γ (-W (list (-● {set p (-not/c 'immutable?)})) sₐ))})
(def-prim string->immutable-string
 (string? . -> . (and/c string? immutable?)))
(def-prim string-length
 (string? . -> . exact-nonnegative-integer?))
(def-prim string-ref (string? exact-nonnegative-integer? . -> . char?))
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
(def-prim string-append (() #:rest (listof string?) . ->* . string?)
  #:refinements
  (() #:rest (listof path-string?) . ->* . path-string?))
(def-prim/custom (string->list ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([W string?])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ V s) W)
  (define sₐ (-?@ 'string->list s))
  (match V
    [(-b "") {set (-ΓA Γ (-W -null.Vs sₐ))}]
    [_
     (define ℒ (-ℒ ∅eq ℓ))
     (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
     (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
     (define Vₜ (-Cons αₕ αₜ))
     (σ⊕V*! Σ [αₕ ↦ (-● {set 'char?})]
            [αₜ ↦ Vₜ]
            [αₜ ↦ -null])
     (define Ans {set (-ΓA Γ (-W (list Vₜ) sₐ))})
     (match V
       [(-b (? string? s)) #:when (> (string-length s) 0) Ans]
       [_ (set-add Ans (-ΓA Γ (-W -null.Vs sₐ)))])]))
(def-prim/custom (list->string ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([W (listof char?)])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ V s) W)
  (define sₐ (-?@ 'list->string s))
  (define ps
    (cond [(list-of-non-null-chars? σ V) ; FIXME needs to check for non-empty-ness too
           {set 'path-string? (-not/c 'immutable?)}]
          [else
           {set 'string? (-not/c 'immutable?)}]))
  {set (-ΓA Γ (-W (list (-● ps)) sₐ))})
(def-prim/todo build-string
 (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . char?) . -> . string?))

;; 4.3.2 String Comparisons. FIXME varargs
(def-preds (string=? string<? string<=? string>? string>=?
            string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?)
 (string? string?))

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
[def-preds (string-contains? string-prefix? string-suffix?)
 (string? string?)]

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
(def-preds (bytes=? bytes<? bytes>?) (bytes? bytes?))

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
(def-preds (char-alphabetic? char-lower-case? char-upper-case? char-title-case?
            char-numeric? char-symbolic? char-punctuation? char-graphic?
            char-whitespace? char-blank? char-iso-control? char-general-category)
 (char?))
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
(def-prim gensym (-> symbol?)) ; FIXME use
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
(def-alias-internal set-mcdr! -set-cdr!) ;; HACK for running some Scheme programs
(def-const null)
(def-prim list? (any/c . -> . boolean?))
(def-prim/todo list (() #:rest list? . ->* . list?))
(def-prim/todo list* ; FIXME
  (-> list?))
; [HO] build-list

;; 4.9.2 List Operations
(def-prim length (list? . -> . exact-nonnegative-integer?))
(def-prim/todo list-ref
 (pair? exact-nonnegative-integer? . -> . any/c))
(def-prim/custom (list-tail ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([Wₗ any/c] [Wₙ exact-nonnegative-integer?])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ Vₗ sₗ) Wₗ)
  (match-define (-W¹ _  sₙ) Wₙ)
  (define sₐ (-?@ 'list-tail sₗ sₙ))
  (match Vₗ
    [(? -St? Vₗ)
     (define Vₕs (extract-list-content σ Vₗ))
     (define ℒ (-ℒ ∅eq ℓ))
     (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
     (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
     (define Vₜ (-Cons αₕ αₜ))
     (for ([Vₕ Vₕs]) (σ⊕V! Σ αₕ Vₕ))
     (σ⊕V*! Σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
     {set (-ΓA Γ (-W -null.Vs sₐ))
          (-ΓA Γ (-W (list Vₜ) sₐ))}]
    [(-b (list))
     {set (-ΓA Γ (-W -null.Vs sₐ))}]
    [_
     {set (-ΓA Γ (-W (list (-● (set 'list?))) sₐ))}]))
(def-prim append (() #:rest (listof list?) . ->* . list?))
#;(def-prim/custom (append ⟪ℋ⟫ ℓ Σ Γ Ws) ; FIXME uses
  #:domain ([W₁ list?] [W₂ list?])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ V₁ s₁) W₁)
  (match-define (-W¹ V₂ s₂) W₂)
  (define sₐ (-?@ 'append s₁ s₂))
  (define Vₐ
    (match* (V₁ V₂)
      [((-b null) V₂) V₂]
      [((-Cons αₕ αₜ) V₂)
       (define ℒ (-ℒ ∅eq ℓ))
       (define αₕ* (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
       (define αₜ* (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
       (for ([Vₕ (σ@ σ αₕ)]) (σ⊕! Σ αₕ* Vₕ))
       (define Vₜs (set-add (σ@ σ αₜ) V₂))
       (for ([Vₜ* Vₜs]) (σ⊕! Σ αₜ* Vₜ*))
       (-Cons αₕ* αₜ*)]
      [(_ _) (-● {set 'list?})]))
  {set (-ΓA Γ (-W (list Vₐ) sₐ))})
(def-prim/custom (reverse ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([Wₗ list?])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ Vₗ sₗ) Wₗ)
  (define sₐ (-?@ 'reverse sₗ))
  (match Vₗ
    [(-b (list)) {set (-ΓA Γ (-W -null.Vs sₐ))}]
    [(-Cons _ _)
     (define ℒ (-ℒ ∅eq ℓ))
     (define αₕ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 0)))
     (define αₜ (-α->⟪α⟫ (-α.fld -𝒾-cons ℒ ⟪ℋ⟫ 1)))
     (define Vₜ (-Cons αₕ αₜ))
     (for ([Vₕ (extract-list-content σ Vₗ)]) (σ⊕V! Σ αₕ Vₕ))
     (σ⊕V*! Σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
     {set (-ΓA Γ (-W (list Vₜ) sₐ))}]
    [(-● ps)
     (cond [(∋ ps -cons?) {set (-ΓA Γ (-W (list (-● {set -cons?})) sₐ))}]
           [else          {set (-ΓA Γ (-W (list (-● {set 'list?})) sₐ))}])]
    [_ {set (-ΓA Γ (-W (list (-● {set 'list?})) sₐ))}]))

;; 4.9.3 List Iteration
#;(def-prim/todo map ; FIXME uses
 (procedure? list? . -> . list?))
#;(def-prims (andmap ormap) ; FIXME uses
 (procedure? list . -> . any/c))
#;(def-prim for-each ; FIXME uses ; FIXME cannot be defined here
 (procedure? list? . -> . void?))
#;(def-prims (foldl foldr) ; FIXME uses
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
(def-prim/custom (member ⟪ℋ⟫ ℓ Σ Γ Ws) ; FIXME uses
  #:domain ([Wₓ any/c] [Wₗ list?])
  (implement-mem 'member ⟪ℋ⟫ ℓ Σ Γ Wₓ Wₗ))
(def-prim/custom (memv ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([Wₓ any/c] [Wₗ list?])
  (implement-mem 'memv ⟪ℋ⟫ ℓ Σ Γ Wₓ Wₗ))
(def-prim/custom (memq ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([Wₓ any/c] [Wₗ list?])
  (implement-mem 'memq ⟪ℋ⟫ ℓ Σ Γ Wₓ Wₗ))
(def-prim/todo memf ; TODO why doc only requires `procedure?` and not `arity-includes 1`
 (procedure? list? . -> . (or/c list? not)))
(def-prim/todo findf
 (procedure? list? . -> . any/c))
(def-prim assoc (any/c (listof pair?) . -> . (or/c pair? not))) ; FIXME uses ; FIXME listof
(def-prims (assv assq) ; FIXME listof
  (any/c (listof pair?) . -> . (or/c pair? not)))
(def-prim/todo assf ; TODO why doc only requires `procedure?`
 (procedure? list? . -> . (or/c pair? not)))

;; 4.9.6 Pair Acesssor Shorthands
; FIXME these are *opaque* for now. Make them composition of accessors
(def-prims (caar cdar)
 ((cons/c pair? any/c) . -> . any/c))
(def-prims (cadr cddr)
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
(def-alias empty null)
(def-alias pair? cons?)
(def-alias empty? null?)
(def-prim first
 ((cons/c any/c list?) . -> . any/c))
(def-prim rest
 ((cons/c any/c list?) . -> . any/c))
(def-prim second
 ((cons/c any/c (cons/c any/c list?)) . -> . any/c))
(def-prim third
 ((cons/c any/c (cons/c any/c (cons/c any/c list?))) . -> . any/c))
(def-prim fourth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))) . -> . any/c))
(def-prim fifth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))) . -> . any/c))
(def-prim sixth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))) . -> . any/c))
(def-prim seventh
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))) . -> . any/c))
(def-prim eighth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))) . -> . any/c))
(def-prim ninth
 ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))))) . -> . any/c))
(def-prim tenth
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
#|(def-alias-internal mpair? -mpair?)
(def-alias-internal mcons -mcons)
(def-alias-internal mcar -mcar)
(def-alias-internal mcdr -mcdr)
(def-alias-internal set-mcar! -set-mcar!)
(def-alias-internal set-mcdr! -set-mcdr!)|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.11 Vectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred vector?)
(def-prim/custom (make-vector ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([Wₙ exact-nonnegative-integer?] [Wᵥ any/c])
  (define σ (-Σ-σ Σ))
  (match-define (-W¹ Vₙ sₙ) Wₙ)
  (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
  (define sₐ (-?@ 'make-vector sₙ sᵥ))
  ;; Heuristic: more concrete vector if length is available concretely
  (match sₙ
    [(-b (? exact-nonnegative-integer? n))
     (define ⟪α⟫s ; with side effect widening store
       (for/list : (Listof ⟪α⟫) ([i (in-range n)])
         (define ⟪α⟫ (-α->⟪α⟫ (-α.idx ℓ ⟪ℋ⟫ (assert i index?))))
         (σ⊕! Σ Γ ⟪α⟫ Wᵥ)
         ⟪α⟫))
     {set (-ΓA Γ (-W (list (-Vector ⟪α⟫s)) sₐ))}]
    [_
     (define ⟪α⟫ (-α->⟪α⟫ (-α.vct ℓ ⟪ℋ⟫)))
     (σ⊕! Σ Γ ⟪α⟫ Wᵥ) ; initializing, not mutating
     {set (-ΓA Γ (-W (list (-Vector^ ⟪α⟫ Vₙ)) sₐ))}]))
(def-prim/custom (vector ⟪ℋ⟫ ℓ Σ Γ Ws)
  (define σ (-Σ-σ Σ))
  (define sₐ (apply -?@ 'vector (map -W¹-s Ws)))
  (define ⟪α⟫s ; with side effect widening store
    (for/list : (Listof ⟪α⟫) ([W (in-list Ws)] [i (in-naturals)])
      (define ⟪α⟫ (-α->⟪α⟫ (-α.idx ℓ ⟪ℋ⟫ (assert i index?))))
      (σ⊕! Σ Γ ⟪α⟫ W)
      ⟪α⟫))
  {set (-ΓA Γ (-W (list (-Vector ⟪α⟫s)) sₐ))})
(def-prim/todo vector-immutable
 (() #:rest list? . ->* . (and/c vector? immutable?)))
(def-prim/custom (vector-length ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([W vector?])
  (match-define (-W¹ V s) W)
  (define sₐ (-?@ 'vector-length s))
  (define A
    (match V
      [(-Vector ⟪α⟫s) (list (-b (length ⟪α⟫s)))]
      [(-Vector^ _ n) (list n)]
      [(-Vector/guard (-Vector/C ⟪α⟫s) _ _) (list (-b (length ⟪α⟫s)))]
      [_ -Nat.Vs]))
  {set (-ΓA Γ (-W A sₐ))})
#;(def-prim/todo vector-ref
 (vector? exact-nonnegative-integer? . -> . any/c))
#;(def-prim/todo vector-set!
 ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?))
(def-prim vector->list (vector? . -> . list?)) ; FIXME retain content
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
  (-> (and/c hash? hash-equal? immutable?)))
(def-prim/todo hasheq ; FIXME uses
  (-> (and/c hash? hash-eq? immutable?)))
(def-prim/todo hasheqv
  (-> (and/c hash? hash-eqv? immutable?)))
(def-prim make-hash ; FIXME uses
  (-> (and/c hash? hash-equal?)))
(def-prim make-hasheqv ; FIXME uses
  (-> (and/c hash? hash-eqv?)))
(def-prim make-hasheq ; FIXME uses ; FIXME listof
  (-> (and/c hash? hash-eq?)))
(def-prim make-weak-hash ; FIXME uses ; FIXME listof
  (-> (and/c hash? hash-equal? hash-weak?)))
(def-prim make-weak-hasheqv ; FIXME uses ; FIXME listof
  (-> (and/c hash? hash-eqv? hash-weak?)))
(def-prim make-weak-hasheq ; FIXME uses ; FIXME listof
  (-> (and/c hash? hash-eq? hash-weak?)))
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
(def-prim make-do-sequence ; FIXME
 (any/c . -> . sequence?))
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
(def-preds (set-equal? set-eqv? set-eq? #:todo set-mutable? set-weak?))
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
(def-prim/custom (procedure-arity ⟪ℋ⟫ ℓ Σ Γ Ws)
  #:domain ([W procedure?])
  (match-define (-W¹ V s) W)
  (define sₐ (-?@ 'procedure-arity s))
  (cond [(V-arity V) => (λ ([a : Arity]) {set (-ΓA Γ (-W (list (-b a)) sₐ))})]
        [else {set (-ΓA Γ (-W -●.Vs sₐ))}]))
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
(def-prim/custom (void ⟪ℋ⟫ ℓ Σ Γ Ws)
  {set (-ΓA Γ -void.W)})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.19 Undefined
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-const undefined)
