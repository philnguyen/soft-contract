#lang racket/base
(require racket/match racket/contract "untyped-utils.rkt")
(provide
 arr? arr*? ctc? dec? impl?
 (contract-out
  [prims (listof dec?)]
  [implications (listof impl?)]
  [base? (ctc? . -> . any)]))

;; FIXME annotation for side effects

(define prims.04
  '(
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.1 Booleans and Equality
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     [#:pred boolean?]
     [#:pred not]
     
     [#:pred equal? (any/c any/c)]
     [#:pred eqv? (any/c any/c)]
     [#:pred eq? (any/c any/c)]
     [#:pred equal?/recur (any/c any/c (any/c any/c . -> . any/c))]
     [#:pred immutable?]
     [gen:equal+hash any/c]
     [prop:equal+hash #|FIXME|# any/c]

     [true  boolean?]
     [false boolean?]
     [#:pred symbol=? (symbol? symbol?)]
     [#:pred boolean=? (boolean? boolean?)]
     [#:alias false? not]
     [xor
      (any/c any/c . -> . any/c)]

     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.2 Numbers
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;;;;; 4.2.1 Number Types
     [#:pred number?]
     [#:alias complex? number?]
     [#:pred real?]
     [#:pred rational?]
     [#:pred integer?]
     [#:pred exact-integer?]
     [#:pred exact-nonnegative-integer?]
     [#:pred exact-positive-integer?]
     [#:pred inexact-real?]
     [#:pred fixnum?]
     [#:pred flonum?]
     [#:pred double-flonum?]
     [#:pred single-flonum?]
     [#:pred zero? (number?)]
     [#:pred positive? (real?)]
     [#:pred negative? (real?)]
     [#:pred even? (integer?)]
     [#:pred odd? (integer?)]
     [#:pred exact? (number?)]
     [#:pred inexact? (number?)]
     [inexact->exact
      (number? . -> . exact?)]
     [exact->inexact
      (number? . -> . inexact?)]
     [real->single-flonum
      (real? . -> . single-flonum?)]
     [real->double-flonum
      (real? . -> . flonum?)]
     
     ;;;;; 4.2.2 Generic Numerics
     
     ;; 4.2.2.1 Arithmetic
     [#:batch (+ - *) ; FIXME var-args
      (number? number? . -> . number?)
      (real? real? . -> . real?)
      (integer? integer? . -> . integer?)]
     [/ ; FIXME varargs
      (number? number? . -> . number?)
      (real? real? . -> . real?)
      #:other-errors
      (any/c (and/c exact? zero?))]
     [#:batch (quotient remainder modulo) ; FIXME: only error on exact 0
      (integer? (and/c integer? (not/c zero?)) . -> . integer?)]
     [quotient/remainder
      (integer? (and/c integer? (not/c zero?)) . -> . (values integer? integer?))]
     [#:batch (add1 sub1)
      (number? . -> . number?)
      (real? . -> . real?)
      (integer? . -> . integer?)]
     [abs
      (real? . -> . real?)
      (integer? . -> . integer?)]
     [#:batch (max min) ; FIXME varargs
      (real? real? . -> . real?)
      (integer? integer? . -> . integer?)]
     [#:batch (gcd lcm) ; FIXME varargs
      (rational? rational? . -> . rational?)]
     [#:batch (round floor ceiling truncate)
      (real? . -> . (or/c integer? (one-of/c +inf.0 -inf.0 +nan.0)))]
     [#:batch (numerator denominator)
      (rational? . -> . integer?)]
     [rationalize
      (real? real? . -> . real?)]

     ;; 4.2.2.2 Number Comparison
     ; FIXME varargs
     [#:pred = (number? number?)] 
     [#:batch (< <= > >=)
      (real? real? . -> . boolean?)]

     ;; 4.2.2.3 Powers and Roots
     [sqrt
      (number? . -> . number?)]
     [integer-sqrt
      (integer? . -> . number?)]
     #;[integer-sqrt/remainder ; FIXME
      (integer? . -> . number? integer?)]
     [expt
      (number? number? . -> . number?)
      #:other-errors
      (zero? negative?)]
     [exp
      (number? . -> . number?)]
     [log
      (number? . -> . number?)]

     ;; 4.2.2.4 Trigonometric Functions
     [#:batch (log sin cos tan asin acos atan)
      (number? . -> . number?)
      (real? . -> . real?)]

     ;; 4.2.2.5 Complex Numbers
     [#:batch (make-rectangular make-polar)
      (real? real? . -> . number?)]
     [#:batch (real-part imag-part)
      (number? . -> . real?)]
     [magnitude
      (number? . -> . (and/c real? (not/c negative?)))]
     [angle
      (number? . -> . real?)]

     ;; 4.2.2.6 Bitwise Operations
     [#:batch (bitwise-ior bitwise-and bitwise-xor) ; FIXME varargs
      (exact-integer? exact-integer? . -> . exact-integer?)]
     [bitwise-not
      (exact-integer? . -> . exact-integer?)]
     [bitwise-bit-set?
      (exact-integer? exact-nonnegative-integer? . -> . boolean?)]
     [bitwise-bit-field ; FIXME `start ≤ end`
      (exact-integer? exact-nonnegative-integer? exact-nonnegative-integer? . -> . integer?)]
     [arithmetic-shift
      (exact-integer? exact-integer? . -> . exact-integer?)]
     [integer-length ; TODO post-con more precise than doc. Confirm.
      (exact-integer? . -> . exact-nonnegative-integer?)]

     ;; 4.2.2.7 Random Numbers
     [random ; FIXME range, all uses
      (integer? pseudo-random-generator? . -> . exact-nonnegative-integer?)]
     [random-seed
      (integer? . -> . void?)]
     [make-pseudo-random-generator
      (-> pseudo-random-generator?)]
     [#:pred pseudo-random-generator?]
     [current-pseudo-random-generator ; FIXME parameter
      (-> pseudo-random-generator?)]
     [pseudo-random-generator->vector
      (pseudo-random-generator? . -> . pseudo-random-generator-vector?)]
     [vector->pseudo-random-generator
      (pseudo-random-generator-vector? . -> . pseudo-random-generator?)]
     [vector->pseudo-random-generator!
      (pseudo-random-generator? pseudo-random-generator-vector? . -> . void?)]
     [#:pred pseudo-random-generator-vector?]

     ;; 4.2.2.8 System-Provided Randomness
     [crypto-random-bytes
      (exact-positive-integer? . -> . bytes?)]

     ;; 4.2.2.9 Number-String Conversions
     [number->string ; FIXME uses
      (number? . -> . string?)]
     [string->number ; FIXME uses
      (string? . -> . (or/c number? not))]
     [real->decimal-string ; FIXME uses
      (real? exact-nonnegative-integer? . -> . string?)]
     [integer-bytes->integer ; FIXME uses
      (bytes? any/c . -> . exact-integer?)]
     [integer->integer-bytes ; FIXME uses
      (exact-integer? (one-of/c 2 4 8) any/c . -> . bytes?)]
     [floating-point-bytes->real ; FIXME uses
      (bytes . -> . flonum?)]
     [real->floating-point-bytes ; FIXME uses
      (real? (one-of/c 2 4 8) . -> . bytes?)]
     [system-big-endian? ; FIXME: opaque or machine dependent? (former probably)
      (-> boolean?)]

     ;; 4.2.2.10 Extra Functions
     [pi   flonum?]
     [pi.f single-flonum?]
     [#:batch (degrees->radians radians->degrees)
      (real? . -> . real?)]
     [sqr
      (number? . -> . number?)
      (real? . -> . real?)
      (integer? . -> . integer?)]
     [sgn
      (real? . -> . (one-of/c -1 0 1 +nan.0 +nan.f))]
     [conjugate
      (number? . -> . number?)]
     [#:batch (sinh cosh tanh)
      (number? . -> . number?)]
     [#:batch (exact-round exact-floor exact-ceiling exact-truncate)
      (rational? . -> . exact-integer?)]
     [order-of-magnitude
      ((and/c real? positive?) . -> . exact-integer?)]
     [#:batch (nan? infinite?)
      (real? . -> . boolean?)]

     ;;;;; 4.2.3 Flonums
     [#:batch (fl+ fl- fl*)
      (flonum? flonum? . -> . flonum?)]
     [fl/
      (flonum? (and/c flonum? (not/c zero?)) . -> . flonum?)]
     [flabs
      (flonum? . -> . (and/c flonum? (not/c negative?)))]
     [#:batch (fl= fl< fl> fl<= fl>=)
      (flonum? flonum? . -> . boolean?)]
     [#:batch (flmin flmax)
      (flonum? flonum? . -> . flonum?)]
     [#:batch (flround flfloor flceiling fltruncate)
      (flonum? . -> . flonum?)]
     [#:batch (flsin flcos fltan flasin flacos flatan fllog flexp flsqrt)
      (flonum? . -> . flonum?)]
     [flexpt ; FIXME accurate behavior for abstract +inf +nan shits
      (flonum? flonum? . -> . flonum?)]
     [->fl
      (exact-integer? . -> . flonum?)]
     [fl->exact-integer?
      (flonum? . -> . exact-integer?)]
     [make-flrectangular ; FIXME precision
      (flonum? flonum? . -> . number?)]
     [#:batch (flreal-part flimag-part) ; FIXME correct domain
      (float-complex? . -> . flonum?)]
     [flrandom ; FIXME range
      (pseudo-random-generator? . -> . flonum?)]

     ;; 4.2.3.2 Flonum Vectors
     [#:pred flvector?]
     #;[flvector
        (-> flvector?)]
     [make-flvector ; FIXME uses
      (exact-nonnegative-integer? flonum? . -> . flvector?)]
     [flvector-length
      (flvector? . -> . exact-nonnegative-integer?)]
     [flvector-ref
      (flvector? exact-nonnegative-integer? . -> . flonum?)]
     [flvector-set!
      (flvector? exact-nonnegative-integer? flonum? . -> . flonum?)]
     [flvector-copy ; FIXME uses
      (flvector? . -> . flvector?)]
     [in-flvector ; FIXME uses
      (flvector? . -> . sequence?)]
     #;[shared-flvector
      (-> flvector?)]
     [make-shared-flvector ; FIXME uses
      (exact-nonnegative-integer? flonum? . -> . flvector?)]

     ;;;;; 4.2.4 Fixnums

     ;; 4.1.4.1 Fixnum Arithmetic
     [#:batch (fx+ fx- fx*)
      (fixnum? fixnum? . -> . fixnum?)]
     [#:batch (fxquotient fxremainder fxmodulo)
      (fixnum? (and/c fixnum? (not/c zero?)) . -> . fixnum?)]
     [fxabs
      (fixnum? . -> . fixnum?)]
     [#:batch (fxand fxior fxxor)
      (fixnum? fixnum? . -> . fixnum?)]
     [fxnot
      (fixnum? . -> . fixnum?)]
     [#:batch (fxlshift fxrshift)
      (fixnum? fixnum? . -> . fixnum?)]
     [#:batch (fx= fx< fx> fx<= fx>=)
      (fixnum? fixnum? . -> . boolean?)]
     [#:batch (fxmin fxmax)
      (fixnum? fixnum? . -> . fixnum?)]
     [fx->fl
      (fixnum? . -> . flonum?)]
     [fl->fx
      (flonum? . -> . fixnum?)]

     ;; 4.2.4.2 Fixnum Vectors
     [#:pred fxvector?]
     #;[fxvector
      (-> fxvector?)]
     [make-fxvector ; FIXME uses
      (exact-nonnegative-integer? fixnum? . -> . fxvector?)]
     [fxvector-length
      (fxvector? . -> . exact-nonnegative-integer?)]
     [fxvector-ref
      (fxvector? exact-nonnegative-integer? . -> . fixnum?)]
     [fxvector-set!
      (fxvector? exact-nonnegative-integer? fixnum? . -> . fixnum?)]
     [fxvector-copy ; FIXME uses
      (fxvector? . -> . fxvector?)]
     [in-fxvector ; FIXME uses
      (fxvector? . -> . sequence?)]
     #;[shared-fxvector
      (-> fxvector?)]
     [make-shared-fxvector ; FIXME uses
      (exact-nonnegative-integer? fixnum? . -> . fxvector?)]

     ;;;;; 4.2.5 Extflonums
     [#:pred extflonum?]
     [extflonum-available?
      (-> boolean?)]

     ;; Extflonum Arithmetic
     [#:batch (extfl+ extfl- extfl*)
      (extflonum? extflonum? . -> . extflonum?)]
     [extfl/
      (extflonum? (and/c extflonum? (not/c zero?)) . -> . extflonum?)]
     [extflabs
      (extflonum? . -> . extflonum?)]
     [#:batch (extfl= extfl< extfl> extfl<= extfl>=)
      (extflonum? extflonum? . -> . boolean?)]
     [#:batch (extflmin extflmax)
      (extflonum? extflonum? . -> . extflonum?)]
     [#:batch (extflround extflfloor extflceiling extfltruncate)
      (extflonum? . -> . extflonum?)]
     [#:batch (extflsin extflcos extfltan extflasin extflacos extflatan
               extfllog extflexp extflsqrt)
      (extflonum? . -> . extflonum?)]
     [extflexpt
      (extflonum? extflonum? . -> . extflonum?)]
     [->extfl
      (exact-integer? . -> . extflonum?)]
     [extfl->exact-integer
      (extflonum? . -> . exact-integer?)]
     [real->extfl
      (real? . -> . extflonum?)]
     [extfl->exact
      (extflonum? . -> . (and/c real? exact?))]
     [extfl->inexact
      (extflonum? . -> . flonum?)]

     ;; 4.2.5.2 Extflonum Constants
     [pi.t extflonum?]
     
     ;; 4.2.5.3 Extflonum Vectors
     [#:pred extflvector?]
     #;[extflvector
      (-> extflvector?)]
     [make-extflvector ; FIXME uses
      (exact-nonnegative-integer? extflonum? . -> . extflvector?)]
     [extflvector-length
      (extflvector? . -> . exact-nonnegative-integer?)]
     [extflvector-ref
      (extflvector? exact-nonnegative-integer? . -> . extflonum?)]
     [extflvector-set!
      (extflvector? exact-nonnegative-integer? extflonum? . -> . extflonum?)]
     [extflvector-copy ; FIXME uses
      (extflvector? . -> . extflvector?)]
     [in-extflvector
      (extflvector? . -> . sequence?)]
     [make-shared-extflvector
      (exact-nonnegative-integer? . -> . extflvector?)]

     ;; 4.2.5.4 Extflonum Byte Strings
     [floating-point-bytes->extfl ; FIXME uses
      (bytes . -> . extflonum?)]
     [extfl->floating-point-bytes
      (extflonum? . -> . bytes?)]
     

     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.3 Strings
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     
     
     ;; 4.3.1 Constructors, Selectors, Mutators
     [#:pred string?]
     [make-string ; FIXME all uses
      (exact-nonnegative-integer? char? . -> . string?)]
     [string
      (() #:rest (listof char?) . ->* . string?)]
     [string->immutable-string
      (string? . -> . (and/c string? immutable?))]
     [string-length
      (string? . -> . exact-nonnegative-integer?)]
     [string-ref
      (string? exact-nonnegative-integer? . -> . char?)]
     [string-set!
      ((and/c string? (not/c immutable?)) exact-nonnegative-integer? char? . -> . void?)]
     [substring ; FIXME uses
      (string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?)]
     [string-copy
      (string . -> . string?)]
     [string-copy! ; FIXME uses
      ((and/c string? (not/c immutable?)) exact-nonnegative-integer? string? . -> . void?)]
     [string-fill! ; FIXME uses
      ((and/c string? (not/c immutable?)) char? . -> . void?)]
     [string-append
      (() #:rest (listof string?) . ->* . string?)]
     [string->list
      (string? . -> . (listof char?))]
     [list->string
      ((listof char?) . -> . string?)]
     [build-string
      (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . char?) . -> . string?)]
     
     ;; 4.3.2 String Comparisons. FIXME varargs
     [#:batch (string=? string<? string<=? string>? string>=?
               string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?)
      (string? string? . -> . boolean?)]

     ;; 4.3.3 String Conversions
     [#:batch (string-upcase string-downcase string-titlecase string-foldcase
               string-normalize-nfd string-normalize-nfkd
               string-normalize-nfc string-normalize-nfkc)
      (string? . -> . string?)]

     ;; 4.3.4 Locale-specific string operations 
     ; FIXME varargs
     [#:batch (string-locale=? string-locale<? string-locale>?
               string-locale-ci=? string-locale-ci<? string-locale-ci>?)
      (string? string? . -> . string?)]
     [#:batch (string-locale-upcase string-locale-downcase)
      (string? . -> . string?)]

     ;; 4.3.5 Additional String Functions
     #;[string-append* #;FIXME]
     [string-join ; FIXME uses
      ((listof string?) . -> . string?)]
     [string-normalize-spaces ; FIXME uses
      (string? . -> . string?)]
     [string-replace ; FIXME uses
      (string? (or/c string? regexp?) string? . -> . string?)]
     [string-split ; FIXME uses
      (string? . -> . (listof string?))]
     [string-trim ; FIXME uses
      (string? . -> . string?)]
     [#:pred non-empty-string?]
     [#:batch (string-contains? string-prefix? string-suffix?)
      (string? string? . -> . boolean?)]

     ;; 4.3.6 Converting Values to Strings.
     [#:batch (~a ~v ~s ~e ~r ~.a ~.v ~.s) ; FIXME uses
      (any/c . -> . string?)]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.4 Byte Strings
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; 4.4.1 Constructors, Selectors, Mutators
     [#:pred bytes?]
     [make-bytes ; FIXME uses
      (exact-nonnegative-integer? byte? . -> . bytes?)]
     #;[bytes
      (-> bytes)]
     [bytes->immutable-bytes
      (bytes? . -> . (and/c bytes? immutable?))]
     [#:pred byte?]
     [bytes-length
      (bytes? . -> . exact-nonnegative-integer?)]
     [bytes-ref
      (bytes exact-nonnegative-integer? . -> . byte?)]
     [bytes-set!
      ((and/c bytes? (not/c immutable?)) exact-nonnegative-integer? byte? . -> . void?)]
     [subbytes ; FIXME uses
      bytes? exact-nonnegative-integer? . -> . bytes?]
     [bytes-copy
      (bytes? . -> . bytes?)]
     [bytes-copy! ; FIXME uses
      ((and/c bytes? (not/c immutable?)) exact-nonnegative-integer? bytes? . -> . void?)]
     [bytes-fill!
      ((and/c bytes? (not/c immutable?)) byte? . -> . void?)]
     [bytes-append
      (() #:rest (listof bytes?) . ->* . bytes?)]
     [bytes->list
      (bytes? . -> . (listof byte?))]
     [list->bytes
      ((listof byte?) . -> . bytes?)]
     [make-shared-bytes ; FIXME uses
      (exact-nonnegative-integer? byte? . -> . bytes?)]
     #;[shared-bytes
      (-> bytes)]

     ;; 4.4.2 Byte String Comparisons
     ; FIXME varargs
     [#:batch (bytes=? bytes<? bytes>?)
      (bytes? bytes? . -> . boolean?)]
     
     ;; 4.4.3 Bytes to/from Characers, Decoding and Encoding
     ; FIXME uses
     [#:batch (bytes->string/utf-8 bytes->string/locale bytes->string/latin-1)
      (bytes? . -> . string?)]
     [#:batch (string->bytes/utf-8 string->bytes/locale string->bytes/latin-1)
      (string? . -> . bytes?)]
     [string-utf-8-length ; FIXME uses
      (string? . -> . exact-nonnegative-integer?)]
     [bytes-utf-8-length ; FIXME uses
      (bytes? . -> . exact-nonnegative-integer?)]
     [#:batch (bytes-utf-8-ref bytes-utf-8-index) ; FIXME uses
      (bytes? exact-nonnegative-integer? . -> . char?)]

     ;; 4.4.4 Bytes to Bytes Encoding Conversion
     [bytes-open-converter
      (string? string? . -> . (or/c bytes-converter? not))]
     [bytes-close-converter
      (bytes-converter? . -> . void?)]
     #;[bytes-convert FIXME
      (bytes-converter? bytes? . -> . any/c)]
     #;[bytes-convert-end]
     [#:pred bytes-converter?]
     [locale-string-encoding
      (-> any/c)]

     ;; 4.4.5 Additional Byte String Functions
     #;[bytes-append*]
     [bytes-join
      ((listof bytes?) bytes? . -> . bytes?)]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.5 Characters
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; 4.5.1 Characters and Scalar Values

     [#:pred char?]
     [char->integer
      (char? . -> . exact-integer?)]
     [integer->char ; FIXME range
      (exact-integer? . -> . char?)]
     [char-utf-8-length ; FIXME range
      (char? . -> . exact-integer?)]
     
     ;; 4.5.2 Comparisons
     [#:batch (char=? char<? char<=? char>? char>=?
               char-ci=? char-ci<? char-ci<=? char-ci>? char-ci>=?) ; FIXME varargs
      (char? char? . -> . boolean?)]
     
     ;; 4.5.3 Classifications
     [#:batch (char-alphabetic? char-lower-case? char-upper-case? char-title-case?
               char-numeric? char-symbolic? char-punctuation? char-graphic?
               char-whitespace? char-blank? char-iso-control? char-general-category)
      (char? . -> . boolean?)]
     [make-known-char-range-list
      (-> (listof (list/c exact-nonnegative-integer?
                         exact-nonnegative-integer?
                         boolean?)))]

     ;; 4.5.4 Character Conversions
     [#:batch (char-upcase char-downcase char-titlecase char-foldcase)
      (char? . -> . char?)]
     
     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.6 Symbols
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     [#:pred symbol?]
     [#:pred symbol-interned? (symbol?)]
     [#:pred symbol-unreadable? (symbol?)]
     [symbol->string
      (symbol? . -> . string?)]
     [#:batch (string->symbol string->uninterned-symbol string->unreadable-symbol)
      (string? . -> . symbol?)]
     [gensym ; FIXME use
      (-> symbol?)]
     [#:pred symbol<? (symbol? symbol?)] ; FIXME varargs


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.7 Regular Expressions
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; 4.7.3 Constructors
     [#:pred regexp?]
     [#:pred pregexp?]
     [#:pred byte-regexp?]
     [#:pred byte-pregexp?]
     [regexp
      (string? . -> . regexp?)]
     [pregexp
      (string? . -> . pregexp?)]
     [byte-regexp
      (bytes? . -> . regexp?)]
     [byte-pregexp
      (bytes? . -> . pregexp?)]
     [regexp-quote ; FIXME uses
      ((or/c string? bytes?) . -> . (or/c string? bytes?))
      (string? . -> . string?)
      (bytes? . -> . bytes?)]
     [regexp-max-lookbehind
      (exact-nonnegative-integer? . -> . (or/c regexp? byte-regexp?))]

     ;; 4.7.4 Regexp Matching
     [regexp-match ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match* ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-try-match ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match-positions ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match-positions* ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match? ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       boolean?)]
     [regexp-match-exact? ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path?)
       . -> .
       boolean?)]
     [regexp-match-peek ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c bytes? (listof (or/c bytes? not)))))]
     [regexp-match-peek-positions ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c (cons/c exact-nonnegative-integer?
                             exact-nonnegative-integer?)
                     (listof (or/c (cons/c exact-nonnegative-integer?
                                           exact-nonnegative-integer?)
                                   not)))
             not))]
     [regexp-match-peek-immediate ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c bytes? (listof (or/c bytes? not)))
             not))]
     [regexp-match-peek-positions-immediate ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c (cons/c exact-nonnegative-integer?
                             exact-nonnegative-integer?)
                     (listof (or/c (cons/c exact-nonnegative-integer?
                                           exact-nonnegative-integer?)
                                   not)))
             not))]
     [regexp-match-peek-positions* ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (listof (cons/c exact-nonnegative-integer?
                             exact-nonnegative-integer?))
             (listof (listof (or/c not (cons/c exact-nonnegative-integer?
                                               exact-nonnegative-integer?))))))]
     [regexp-match/end
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
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
     [regexp-split ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? input-port?)
       . -> .
       any/c)]

     ;; 4.7.6 Regexp Substitution
     [regexp-replace ; FIXME uses, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes?)
       (or/c string? bytes? #|TODO more|#)
       . -> .
       any/c)]
     [regexp-replace* ; FIXME uses
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes?)
       (or/c string? bytes? #|TODO more|#)
       . -> .
       (or/c string? bytes?))]
     [regexp-replaces
      ((or/c string? bytes?)
       (listof
        (list/c (or/c string? bytes regexp? byte-regexp?)
                (or/c string bytes? #|TODO more|#)))
       . -> .
       (or/c string? bytes?))]
     [regexp-replace-quote
      ((or/c string? bytes?) . -> . (or/c string? bytes?))
      (string? . -> . string?)
      (bytes? . -> . bytes?)]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.8 Keywords
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:pred keyword?]
     [keyword->string
      (keyword? . -> . string?)]
     [string->keyword
      (string? . -> . keyword?)]
     [#:pred keyword<? (keyword? keyword?)] ; FIXME varargs

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.9 Pairs and Lists
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; 4.9.1 Constructors and Selectors
     [#:struct-pred pair? (cons #f #f)]
     [#:pred null?]
     [#:struct-cons cons (cons #f #f)]
     [#:struct-acc car (cons #f #f) 0]
     [#:struct-acc cdr (cons #f #f) 1]
     [null null?]
     [#:pred list?]
     [list (() #:rest list? . ->* . list?)]
     #;[list* ; FIXME
      (-> list?)]
     [build-list
      (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . any/c) . -> . list?)]

     ;; 4.9.2 List Operations
     [length
      (list? . -> . exact-nonnegative-integer?)]
     [list-ref
      (pair? exact-nonnegative-integer? . -> . any/c)]
     [list-tail
      (any/c exact-nonnegative-integer? . -> . any/c)]
     [append ; FIXME uses
      (list? list? . -> . list?)]
     [reverse
      (list? . -> . list?)]

     ;; 4.9.3 List Iteration
     [map ; FIXME uses
      (procedure? list? . -> . list?)]
     [#:batch (andmap ormap) ; FIXME uses
      (procedure? list . -> . any/c)]
     [for-each ; FIXME uses
      (procedure? list? . -> . void?)]
     [#:batch (foldl foldr) ; FIXME uses
      (procedure? any/c list? . -> . any/c)]
     
     ;; 4.9.4 List Filtering
     [filter
      ((any/c . -> . any/c) list? . -> . list?)]
     [remove ; FIXME uses
      (any/c list? . -> . list?)]
     [#:batch (remq remv)
      (any/c list? . -> . list?)]
     [remove* ; FIXME uses
      (list? list? . -> . list?)]
     [#:batch (remq* remv*)
      (list? list? . -> . list?)]
     [sort ; FIXME uses
      (list? (any/c any/c . -> . any/c) . -> . list?)]
     
     ;; 4.9.5 List Searching
     [member ; FIXME uses
      (any/c list? . -> . (or/c list? not))]
     [#:batch (memv memq)
      (any/c list? . -> . (or/c list? not))]
     [memf ; TODO why doc only requires `procedure?` and not `arity-includes 1`
      (procedure? list? . -> . (or/c list? not))]
     [findf
      (procedure? list? . -> . any/c)]
     [assoc ; FIXME uses
      (any/c (listof pair?) . -> . (or/c pair? not))]
     [#:batch (assv assq)
      (any/c (listof pair?) . -> . (or/c pair? not))]
     [assf ; TODO why doc only requires `procedure?`
      (procedure? list? . -> . (or/c pair? not))]

     ;; 4.9.6 Pair Acesssor Shorthands
     ; FIXME these are *opaque* for now. Make them composition of accessors
     [#:batch (caar cdar)
      ((cons/c pair? any/c) . -> . any/c)]
     [#:batch (cadr cddr)
      ((cons/c any/c pair?) . -> . any/c)]
     [caaar
      ((cons/c (cons/c pair? any/c) any/c) . -> . any/c)]
     [caadr
      ((cons/c any/c (cons/c pair? any/c)) . -> . any/c)]
     [cadar
      ((cons/c (cons/c any/c pair?) any/c) . -> . any/c)]
     [caddr
      ((cons/c any/c (cons/c any/c pair?)) . -> . any/c)]
     [cdaar
      ((cons/c (cons/c pair? any/c) any/c) . -> . any/c)]
     [cdadr
      ((cons/c any/c (cons/c pair? any/c)) . -> . any/c)]
     [cddar
      ((cons/c (cons/c any/c pair?) any/c) . -> . any/c)]
     [cdddr
      ((cons/c any/c (cons/c any/c pair?)) . -> . any/c)]
     ; TODO rest of them

     ;; 4.9.7 Additional List Functions and Synonyms
     [#:alias empty null]
     [#:alias cons? pair?]
     [#:alias empty? null?]
     [first
      ((cons/c any/c list?) . -> . any/c)]
     [rest
      ((cons/c any/c list?) . -> . any/c)]
     [second
      ((cons/c any/c (cons/c any/c list?)) . -> . any/c)]
     [third
      ((cons/c any/c (cons/c any/c (cons/c any/c list?))) . -> . any/c)]
     [fourth
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))) . -> . any/c)]
     [fifth
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))) . -> . any/c)]
     [sixth
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))) . -> . any/c)]
     [seventh
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))) . -> . any/c)]
     [eighth
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))) . -> . any/c)]
     [ninth
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?))))))))) . -> . any/c)]
     [tenth
      ((cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c (cons/c any/c list?)))))))))) . -> . any/c)]
     [last
      ((and/c list? (not/c empty?)) . -> . any/c)]
     [last-pair
      (pair? . -> . pair?)]
     [make-list
      (exact-nonnegative-integer? any/c . -> . list?)]
     [list-update ; FIXME range
      (list? exact-nonnegative-integer? (any/c . -> . any/c) . -> . list?)]
     [list-set ; FIXME range
      (list? exact-nonnegative-integer? any/c . -> . list?)]
     [take ; FIXME range
      (list? exact-nonnegative-integer? . -> . list?)]
     [drop
      (any/c exact-nonnegative-integer? . -> . any/c)]
     #;[split-at ; FIXME
      (any/c exact-nonnegative-integer? . -> . (values list? any/c))]
     [takef
      (any/c procedure? . -> . list?)]
     [dropf
      (any/c procedure? . -> . any/c)]
     [splitf-at ; FIXME
      (any/c procedure? . -> . (values list? any/c))]
     [take-right
      (any/c exact-nonnegative-integer? . -> . any/c)]
     [drop-right
      (any/c exact-nonnegative-integer? . -> . list?)]
     #;[split-at-right ; FIXME
      (any/c exact-nonnegative-integer? . -> . (values list? any/c))]
     [takef-right
      (any/c procedure? . -> . list?)]
     [dropf-right
      (any/c procedure? . -> . any/c)]
     #;[splitf-at-right ; FIXME uses
      (any/c procedure? . -> . (values list? any/c))]
     [list-prefix? ; FIXME uses
      (list? list? . -> . boolean?)]
     [take-common-prefix ; FIXME uses
      (list? list? . -> . list?)]
     #;[drop-common-prefix ; FIXME uses
      (list? list? . -> . (values list? list?))]
     #;[split-common-prefix ; FIXME uses
      (list? list? . -> . (values list? list? list?))]
     [add-between ; FIXME uses
      (list? any/c . -> . list?)]
     [append* ; FIXME uses
      ((listof list?) . -> . list?)]
     [flatten
      (any/c . -> . list?)]
     [check-duplicates ; FIXME uses
      (list? . -> . any/c)] ; simplified from doc's `(or/c any/c #f)`
     [remove-duplicates ; FIXME uses
      (list? . -> . list?)]
     [filter-map ; FIXME uses
      (procedure? list? . -> . list?)]
     [count ; FIXME varargs
      (procedure? list? . -> . exact-nonnegative-integer?)]
     #;[partition
      (procedure? list? . -> . (values list? list?))]
     [range ; FIXME uses
      (real? . -> . list?)]
     [append-map ; FIXME varargs
      (procedure? list? . -> . list?)]
     [filter-not
      ((any/c . -> . any/c) list? . -> . list?)]
     [shuffle
      (list? . -> . list?)]
     [permutations
      (list? . -> . list?)]
     [in-permutations
      (list? . -> . sequence?)]
     [#:batch (argmin argmax)
      ((any/c . -> . real?) (and/c pair? list?) . -> . any/c)]
     [group-by ; FIXME uses
      ((any/c . -> . any/c) list? . -> . (listof list?))]
     [cartesian-product ; FIXME varargs
      (() #:rest (listof list?) . ->* . (listof list?))]
     [remf
      (procedure? list? . -> . list?)]
     [remf*
      (procedure? list? . -> . list?)]

     ;; 4.9.8 Immutable Cyclic Data
     [make-reader-graph
      (any/c . -> . any/c)]
     [#:pred placeholder?]
     [make-placeholder
      (any/c . -> . placeholder?)]
     [placeholder-set!
      (placeholder? any/c . -> . void?)]
     [placeholder-get
      (placeholder? . -> . any/c)]
     [#:pred hash-placeholder?]
     [#:batch (make-hash-placeholder make-hasheq-placeholder make-hasheqv-placeholder)
      ((listof pair?) . -> . hash-placeholder?)]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.10 Mutable Pairs and Lists
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.11 Vectors
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:pred vector?] ; FIXME alias for internal `vector?`
     [make-vector
      (exact-nonnegative-integer? any/c . -> . vector?)]
     [vector
      (() #:rest list? . ->* . (and/c vector? (not/c immutable?)))]
     [vector-immutable
      (() #:rest list? . ->* . (and/c vector? immutable?))]
     [vector-length
      (vector? . -> . exact-nonnegative-integer?)]
     [vector-ref
      (vector? exact-nonnegative-integer? . -> . any/c)]
     [vector-set!
      ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?)]
     [vector->list
      (vector? . -> . list?)]
     [list->vector
      (list? . -> . vector?)]
     [vector->immutable-vector
      (vector? . -> . (and/c vector? immutable?))]
     [vector-fill!
      ((and/c vector? (not/c immutable?)) any/c . -> . void?)]
     [vector-copy! ; FIXME uses
      ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? vector? . -> . void?)]
     #;[vector->values ; FIXME uses, var-values, `any` instead of `any/c`
      (vector? exact-nonnegative-integer? exact-nonnegative-integer? . -> . any)]
     [build-vector
      (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . any/c)
                                  . -> . (and/c vector? (not/c immutable?)))]

     ;; 4.11.1 Additional Vector Functions
     [vector-set*! ; FIXME uses
      ((and/c vector? (not/c immutable?)) exact-nonnegative-integer? any/c . -> . void?)]
     [vector-map ; FIXME uses
      (procedure? vector? . -> . vector?)]
     [vector-map! ; FIXME uses
      (procedure? (and/c vector? (not/c immutable?)) . -> . vector?)]
     [vector-append
      (() #:rest (listof vector?) . ->* . vector?)]
     [vector-take
      (vector? exact-nonnegative-integer? . -> . vector?)]
     [vector-take-right
      (vector? exact-nonnegative-integer? . -> . vector?)]
     [vector-drop
      (vector? exact-nonnegative-integer? . -> . vector?)]
     [vector-drop-right
      (vector? exact-nonnegative-integer? . -> . vector?)]
     [vector-split-at
      (vector? exact-nonnegative-integer? . -> . (values vector? vector?))]
     [vector-split-at-right
      (vector? exact-nonnegative-integer? . -> . (values vector? vector?))]
     [vector-copy ; FIXME uses
      (vector? . -> . vector?)]
     [#:batch (vector-filter vector-filter-not)
      ((any/c . -> . any/c) vector? . -> . vector?)]
     [vector-count ; FIXME varargs
      (procedure? vector? . -> . exact-nonnegative-integer?)]
     [#:batch (vector-argmin vector-argmax)
      ((any/c . -> . real?) vector? . -> . any/c)]
     [#:batch (vector-member vector-memv vector-memq)
      (any/c vector? . -> . (or/c exact-nonnegative-integer? not))]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.12 Boxes
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:struct-pred box? (box #t)]
     [#:struct-cons box (box #t)]
     ;[#:struct-cons box-immutable (box #f)]
     [#:struct-acc unbox (box #t) 0]
     [#:struct-mut set-box! (box #t) 0]
     #;[box-cas!]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.13 Hash Tables
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:pred hash?]
     [#:batch (hash-equal? hash-eqv? hash-eq? hash-weak?)
      (hash? . -> . boolean?)]
     [hash ; FIXME uses
      (any/c any/c . -> . (and/c hash? hash-equal? immutable?))]
     [hasheq ; FIXME uses
      (any/c any/c . -> . (and/c hash? hash-eq? immutable?))]
     [hasheqv
      (any/c any/c . -> . (and/c hash? hash-eqv? immutable?))]
     [make-hash ; FIXME uses
      ((listof pair?) . -> . (and/c hash? hash-equal?))]
     [make-hasheqv ; FIXME uses
      ((listof pair?) . -> . (and/c hash? hash-eqv?))]
     [make-hasheq ; FIXME uses
      ((listof pair?) . -> . (and/c hash? hash-eq?))]
     [make-weak-hash ; FIXME uses
      ((listof pair?) . -> . (and/c hash? hash-equal? hash-weak?))]
     [make-weak-hasheqv ; FIXME uses
      ((listof pair?) . -> . (and/c hash? hash-eqv? hash-weak?))]
     [make-weak-hasheq ; FIXME uses
      ((listof pair?) . -> . (and/c hash? hash-eq? hash-weak?))]
     [hash-set!
      ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?)]
     [hash-set*! ; FIXME uses
      ((and/c hash? (not/c immutable?)) any/c any/c . -> . void?)]
     [hash-set ; FIXME refine with `eq?` and `eqv?`
      ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?))]
     [hash-set* ; FIXME refine with `eq?` and `eqv?`
      ((and/c hash? immutable?) any/c any/c . -> . (and/c hash? immutable?))]
     [hash-ref ; FIXME uses
      (hash? any/c . -> . any/c)]
     [hash-ref! ; FIXME precision
      (hash? any/c any/c . -> . any/c)]
     [hash-has-key?
      (hash? any/c . -> . boolean?)]
     [hash-update! ; FIXME uses
      ((and/c hash? (not/c immutable?)) any/c (any/c . -> . any/c) . -> . void?)]
     [hash-update
      ((and/c hash? immutable?) any/c (any/c . -> . any/c) . -> . (and/c hash? immutable?))]
     [hash-remove!
      ((and/c hash? (not/c immutable?)) any/c . -> . void?)]
     [hash-remove
      ((and/c hash? immutable?) any/c . -> . (and/c hash? immutable?))]
     [hash-clear!
      ((and/c hash? (not/c immutable?)) . -> . void?)]
     [hash-clear
      ((and/c hash? immutable?) . -> . (and/c hash? immutable?))]
     [hash-copy-clear
      (hash? . -> . hash?)]
     [hash-map ; FIXME uses
      (hash? (any/c any/c . -> . any/c) . -> . (listof any/c))]
     [hash-keys
      (hash? . -> . (listof any/c))]
     [hash-values
      (hash? . -> . (listof any/c))]
     [hash->list ; simplified from doc's `(cons/c any/c any/c)`
      (hash? . -> . (listof pair?))]
     [hash-for-each ; FIXME uses
      (hash? (any/c any/c . -> . any) . -> . void?)]
     [hash-count
      (hash? . -> . exact-nonnegative-integer?)]
     [hash-empty?
      (hash? . -> . boolean?)]
     [hash-iterate-first
      (hash? . -> . (or/c exact-nonnegative-integer? not))]
     [hash-iterate-next
      (hash? exact-nonnegative-integer? . -> . (or/c exact-nonnegative-integer? not))]
     [#:batch (hash-iterate-key hash-iterate-value)
      (hash? exact-nonnegative-integer? . -> . any/c)]
     [hash-copy
      (hash? . -> . (and/c hash? (not/c immutable?)))]
     [#:batch (eq-hash-code eqv-hash-code equal-hash-code equal-secondary-hash-code)
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
     [#:pred sequence?]
     [in-range ; FIXME uses
      (real? . -> . stream?)]
     [in-naturals ; FIXME uses
      (exact-nonnegative-integer? . -> . stream?)]
     [in-list
      (list? . -> . stream?)]
     #;[in-mlist ; FIXME don't know about `mlist?`
      (mlist? . -> . stream?)]
     [in-vector ; FIXME uses
      (vector? . -> . sequence?)]
     [in-string ; FIXME uses
      (string? . -> . sequence?)]
     [in-bytes ; FIXME uses
      (bytes? . -> . sequence?)]
     [in-port ; FIXME uses
      ((input-port? . -> . any/c) input-port? . -> . sequence?)]
     [in-input-port-bytes
      (input-port? . -> . sequence?)]
     [in-input-port-chars
      (input-port? . -> . sequence?)]
     [in-lines ; FIXME uses
      (input-port? (one-of/c 'linefeed 'return 'return-linefeed 'any 'any-one)
                   . -> . sequence?)]
     [in-bytes-lines ; FIXME uses
      (input-port? (one-of/c 'linefeed 'return 'return-linefeed 'any 'any-one)
                   . -> . sequence?)]
     [in-hash
      (hash? . -> . sequence?)]
     [#:batch (in-hash-keys in-hash-values)
      (hash? . -> . sequence?)]
     [in-hash-pairs
      (hash? . -> . sequence?)]
     [in-directory ; FIXME uses
      ((or/c path-string? not) . -> . sequence?)]
     [in-producer ; FIXME uses
      (procedure? . -> . sequence?)]
     [in-value
      (any/c . -> . sequence?)]
     [in-indexed
      (sequence? . -> . sequence?)]
     [in-sequences
      (() #:rest (listof sequence?) . ->* . sequence?)]
     [in-cycle
      (() #:rest (listof sequence?) . ->* . sequence?)]
     [in-parallel
      (() #:rest (listof sequence?) . ->* . sequence?)]
     [in-values-sequence
      (sequence? . -> . sequence?)]
     [in-values*-sequence
      (sequence? . -> . sequence?)]
     [#:batch (stop-before stop-after)
      (sequence? (any/c . -> . any/c) . -> . sequence?)]
     [make-do-sequence
      ((-> (values (any/c . -> . any/c)
                   (any/c . -> . any/c)
                   any/c
                   (or/c (any/c . -> . any/c) not)
                   ; FIXME optional arg
                   #;(or/c (() () #:rest list? . ->* . any/c) not)
                   #;(or/c ((any/c) () #:rest list? . ->* . any/c) not)))
       . -> . sequence?)]
     [prop:sequence struct-type-property?]

     ;; 4.14.1.2 Sequence Conversion
     [sequence->stream
      (sequence? . -> . stream?)]
     [sequence-generate
      (sequence? . -> . (values (-> boolean?) (-> any)))]
     [sequence-generate*
      (sequence? . -> . (values (or/c list? not)
                                (-> (values (or/c list? not) procedure?))))]
     
     ;; 4.14.1.3 Additional Sequence Operations
     [empty-sequence sequence?]
     [sequence->list
      (sequence? . -> . list?)]
     [sequence-length
      (sequence? . -> . exact-nonnegative-integer?)]
     [sequence-ref
      (sequence? exact-nonnegative-integer? . -> . any)]
     [sequence-tail
      (sequence? exact-nonnegative-integer? . -> . sequence?)]
     [sequence-append
      (() #:rest (listof sequence?) . ->* . sequence?)]
     [sequence-map
      ((any/c . -> . any/c) sequence? . -> . sequence?)]
     [#:batch (sequence-andmap sequence-ormap) ; FIXME generalize 1st arg to multi args
      ((any/c . -> . boolean?) sequence? . -> . boolean?)]
     [sequence-for-each ; FIXME generalize 1st arg to multi args
      ((any/c . -> . any) sequence? . -> . void?)]
     [sequence-fold ; FIXME generalize 1st arg
      ((any/c any/c . -> . any/c) any/c sequence? . -> . any/c)]
     [sequence-count ; FIXME precise arity for 1st arg
      (procedure? sequence? . -> . exact-nonnegative-integer?)]
     [sequence-filter ; FIXME generalize 1st arg to multi args
      ((any/c . -> . boolean?) sequence? . -> . sequence?)]
     [sequence-add-between
      (sequence? any/c . -> . sequence?)]
     #;[sequence/c ; FIXME uses, `contract?`
      (any/c . -> . any/c)]

     ; 4.14.1.3.1 Additional Sequence Constructors
     #;[in-syntax
      (syntax? . -> . sequence?)]
     [in-slice
      (exact-positive-integer? sequence? . -> . sequence?)]

     ;;;;; 4.14.2 Streams
     [#:pred stream?]
     [#:pred stream-empty? (stream?)]
     [stream-first
      ((and/c stream? (not/c stream-empty?)) . -> . any)]
     [stream-rest
      ((and/c stream? (not/c stream-empty?)) . -> . stream?)]
     [in-stream
      (stream? . -> . sequence?)]
     [empty-stream stream?]
     [stream->list
      (stream? . -> . list?)]
     [stream-length
      (stream? . -> . exact-nonnegative-integer?)]
     [stream-ref
      (stream? exact-nonnegative-integer? . -> . any)]
     [stream-tail
      (stream? exact-nonnegative-integer? . -> . stream?)]
     [stream-append
      (() #:rest (listof stream?) . ->* . stream?)]
     [stream-map
      (procedure? stream? . -> . stream?)]
     [#:batch (stream-andmap stream-ormap) ; FIXME varargs on 1st
      ((any/c . -> . boolean?) stream? . -> . boolean?)]
     [stream-for-each ; FIXME varargs on 1st
      ((any/c . -> . any) stream? . -> . void?)]
     [stream-fold ; FIXME varargs on 1st
      ((any/c any/c . -> . any) any/c stream? . -> . any/c)]
     [stream-count ; FIXME varargs on 1st
      (procedure? stream? . -> . exact-nonnegative-integer?)]
     [stream-filter ; FIXME varargs on 1st
      ((any/c . -> . boolean?) stream? . -> . stream?)]
     [stream-add-between
      (stream? any/c . -> . stream?)]
     [prop:stream struct-type-property?]
     [stream/c
      (contract? . -> . contract?)]

     ;;;;; 4.14.3 Generators
     [#:pred generator?]
     #;[yield ; FIXME uses
      (-> any)]
     [generator-state
      (generator? . -> . symbol?)]
     [sequence->generator
      (sequence? . -> . (-> any))]
     [sequence->repeated-generator
      (sequence? . -> . (-> any))]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.15 Dictionaries
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;;;;; 4.15.1 Dictionary Predicates and Contracts
     [#:pred dict?]
     [dict-implements? ; FIXME varargs
      (dict? symbol? . -> . boolean?)]
     #;[dict-implements/c ; FIXME varargs, contracts
      (symbol? . -> . flat-contract?)]
     [#:pred dict-mutable? (dict?)]
     [#:pred dict-can-remove-keys? (dict?)]
     [#:pred dict-can-functional-set? (dict?)]

     ;;;;; 4.15.2 Generic Dictionary Interface
     [prop:dict struct-type-property?]
     
     ;; 4.15.2.1 Primitive Dictionary Methods
     [dict-ref ; FIXME use
      (dict? any/c . -> . any)]
     [dict-set!
      ((and/c dict? (not/c immutable?)) any/c any/c . -> . void?)]
     [dict-set
      ((and/c dict? immutable?) any/c any/c . -> . (and/c dict? immutable?))]
     [dict-remove!
      ((and/c dict? (not/c immutable?)) any/c . -> . void?)]
     [dict-remove
      ((and/c dict? immutable?) any/c . -> . (and/c dict? immutable?))]
     [dict-iterate-first
      (dict? . -> . any/c)]
     [dict-iterate-next
      (dict? any/c . -> . any/c)]
     [dict-iterate-key
      (dict? any/c . -> . any)]
     [dict-iterate-value
      (dict? any/c . -> . any)]

     ;; 4.15.2.2 Derived Dictionary Methods
     [#:pred dict-has-key? (dict? any/c)]
     [dict-set*! ; FIXME use
      ((and/c dict? (not/c immutable?)) any/c any/c . -> . void?)]
     [dict-set* ; FIXME use
      ((and/c dict? immutable?) any/c any/c . -> . (and/c dict? immutable?))]
     [dict-ref!
      (dict? any/c any/c . -> . any)]
     [dict-update! ; FIXME use
      ((and/c dict? (not/c immutable?)) any/c (any/c . -> . any/c) . -> . void?)]
     [dict-update
      ((and/c dict? immutable?) any/c (any/c . -> . any/c) . -> . (and/c dict? immutable?))]
     [dict-map
      (dict? (any/c any/c . -> . any/c) . -> . (listof any/c))]
     [dict-for-each
      (dict? (any/c any/c . -> . any) . -> . void?)]
     [#:pred dict-empty? (dict?)]
     [dict-count
      (dict? . -> . exact-nonnegative-integer?)]
     [dict-copy
      (dict? . -> . dict?)]
     [dict-clear
      (dict? . -> . dict?)]
     [dict-clear!
      (dict? . -> . void?)]
     [#:batch (dict-keys dict-values)
      (dict? . -> . list?)]
     [dict->list ; TODO more precise than doc. Confirm.
      (dict? . -> . (listof pair?))]

     ;;;;; 4.15.3 Dictionary Sequences
     [in-dict
      (dict? . -> . sequence?)]
     [#:batch (in-dict-keys in-dict-values)
      (dict? . -> . sequence?)]
     [in-dict-pairs
      (dict? . -> . sequence?)]
     
     ;;;;; 4.15.4 Contracted Dictionaries
     [prop:dict/contract struct-type-property?]
     #;[#:batch (dict-key-contract dict-value-contract dict-iter-contract) ; FIXME contract?
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
     [#:batch (make-custom-hash make-weak-custom-hash make-immutable-custom-hash) ; FIXME uses
      ((or/c (any/c any/c . -> . any/c)
             (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
       . -> . dict?)]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.16 Sets
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     
     ;;;;; Hash Sets
     [#:pred set-equal?]
     [#:pred set-eqv?]
     [#:pred set-eq?]
     [#:pred set?]
     [#:pred set-mutable?]
     [#:pred set-weak?]
     [set
      (() #:rest list? . ->* . (and/c generic-set? set-equal? set?))]
     [seteqv
      (() #:rest list? . ->* . (and/c generic-set? set-eqv? set?))]
     [seteq
      (() #:rest list? . ->* . (and/c generic-set? set-eq? set?))]
     [mutable-set
      (() #:rest list? . ->* . (and/c generic-set? set-equal? set-mutable?))]
     [mutable-seteqv
      (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-mutable?))]
     [mutable-seteq
      (() #:rest list? . ->* . (and/c generic-set? set-eq? set-mutable?))]
     [weak-set
      (() #:rest list? . ->* . (and/c generic-set? set-equal? set-weak?))]
     [weak-seteqv
      (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-weak?))]
     [weak-seteq
      (() #:rest list? . ->* . (and/c generic-set? set-eq? set-weak?))]
     [list->set
      (list? . -> . (and/c generic-set? set-equal? set?))]
     [list->seteqv
      (list? . -> . (and/c generic-set? set-eqv? set?))]
     [list->seteq
      (list? . -> . (and/c generic-set? set-eq? set?))]
     [list->mutable-set
      (list? . -> . (and/c generic-set? set-equal? set-mutable?))]
     [list->mutable-seteqv
      (list? . -> . (and/c generic-set? set-eqv? set-mutable?))]
     [list->mutable-seteq
      (list? . -> . (and/c generic-set? set-eq? set-mutable?))]
     [list->weak-set
      (list? . -> . (and/c generic-set? set-equal? set-weak?))]
     [list->weak-seteqv
      (list? . -> . (and/c generic-set? set-eqv? set-weak?))]
     [list->weak-seteq
      (list? . -> . (and/c generic-set? set-eq? set-weak?))]

     ;;;;; 4.16.2 Set Predicates and Contracts
     [#:pred generic-set?]
     [set-implements
      ((generic-set?) #:rest (listof symbol?) . ->* . boolean?)]
     #;[set-implements/c ; FIXME varargs, contract?
      (symbol? . -> . flat-contract?)]
     #;[set/c ; FIXME uses, contract?
      (chaperone-contract? . -> . contract?)]

     ;;;;; 4.16.3 Generic Set Interface

     ;; 4.16.3.1 Set Methods
     [#:pred set-member? (generic-set? any/c)]
     [#:batch (set-add set-remove)
      ((and/c generic-set? (not/c set-mutable?)) any/c . -> . generic-set?)]
     [#:batch (set-add! set-remove!)
      ((and/c generic-set? set-mutable?) any/c . -> . void?)]
     [#:pred set-empty? (generic-set?)]
     [set-count
      (generic-set? . -> . exact-nonnegative-integer?)]
     [set-first
      ((and/c generic-set? (not/c set-empty?)) . -> . any/c)]
     [set-rest ; TODO probably refine with (im)mutable? and other modifiers
      ((and/c generic-set? (not/c set-empty?)) . -> . generic-set?)]
     [set->stream
      (generic-set? . -> . stream?)]
     [set-copy
      (generic-set? . -> . generic-set?)]
     [set-copy-clear
      (generic-set? . -> . (and/c generic-set? set-empty?))]
     [set-clear
      ((and/c generic-set? (not/c set-mutable?)) . -> . (and/c generic-set? set-empty?))]
     [set-clear!
      ((and/c generic-set? set-mutable?) . -> . void?)]
     [set-union ; FIXME enforce sets of the same type
      ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?)]
     [set-union! ; FIXME enforce sets of the same type
      ((generic-set?) #:rest (listof generic-set?) . ->* . void?)]
     [set-intersect
      ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?)]
     [set-intersect!
      ((generic-set?) #:rest (listof generic-set?) . ->* . void?)]
     [set-subtract
      ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?)]
     [set-subtract!
      ((generic-set?) #:rest (listof generic-set?) . ->* . void?)]
     [set-symmetric-difference
      ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?)]
     [set-symmetric-difference!
      ((generic-set?) #:rest (listof generic-set?) . ->* . void?)]
     [#:batch (set=? subset? proper-subset?) ; FIXME enforce same `set` type
      (generic-set? generic-set? . -> . boolean?)]
     [set->list
      (generic-set? . -> . list?)]
     [set-map
      (generic-set? (any/c . -> . any/c) . -> . (listof any/c))]
     [set-for-each
      (generic-set? (any/c . -> . any) . -> . void?)]
     [in-set
      (generic-set? . -> . sequence?)]

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
     [#:pred procedure?]
     [apply ; FIXME uses. This probably should be treated specially for precision
      (procedure? (listof any/c) . -> . any)]
     [compose ; FIXME uses
      ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any))]
     [compose1 ; FIXME uses
      ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any))]
     [procedure-rename
      (procedure? symbol? . -> . procedure?)]
     [procedure->method
      (procedure? . -> . procedure?)]
     [#:pred procedure-closure-contents-eq? (procedure? procedure?)]

     ;; 4.17.1 Keywords and Arity
     ;[keyword-apply #|FIXME uses|#]
     [procedure-arity
      (procedure? . -> . normalized-arity?)]
     [#:pred procedure-arity?]
     [#:pred procedure-arity-includes? (procedure? exact-nonnegative-integer?)] ; FIXME uses
     [procedure-reduce-arity
      (procedure? procedure-arity? . -> . procedure?)]
     [procedure-keywords
      (procedure? . -> . (values (listof keyword?) (or/c (listof keyword?) not)))]
     #;[make-keyword-procedure ; FIXME uses
      ((((listof keyword?) list?) () #:rest list? . ->* . any) . -> . procedure?)]
     [procedure-reduce-keyword-arity
      (procedure? procedure-arity? (listof keyword?) (or/c (listof keyword?) not)
                  . -> . procedure?)]
     [#:pred arity-at-least?]
     [arity-at-least (exact-nonnegative-integer? . -> . arity-at-least?)]
     [arity-at-least-value (arity-at-least? . -> . exact-nonnegative-integer?)]
     [#:alias make-arity-at-least arity-at-least]
     [prop:procedure struct-type-property?]
     [#:pred procedure-struct-type? (struct-type?)]
     [procedure-extract-target
      (procedure? . -> . (or/c procedure? not))]
     [prop:arity-string struct-type-property?]
     [prop:checked-procedure struct-type-property?]
     [checked-procedure-check-and-extract
      (struct-type? any/c (any/c any/c any/c . -> . any/c) any/c any/c . -> . any/c)]

     ;; 4.17.2 Reflecting on Primitives
     [#:pred primitive?]
     [#:pred primitive-closure?]
     [primitive-result-arity
      (primitive? . -> . procedure-arity?)]
     
     ;; 4.17.3 Additional Higher-Order Functions
     [identity (any/c . -> . any/c)]
     [const (any . -> . procedure?)]
     [negate (procedure? . -> . procedure?)]
     ;[curry ] FIXME
     ;[curryr] FIXME
     [#:pred normalized-arity?]
     [normalize-arity ; FIXME dependency
      (procedure-arity? . -> . normalized-arity?)]
     [#:pred arity=? (procedure-arity? procedure-arity?)]
     [#:pred arity-includes? (procedure-arity? procedure-arity?)]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.18 Void
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:pred void?]
     [void (() #:rest list? . ->* . void?)]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.19 Undefined
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [undefined any/c]
))

(define prims.08
  ;; FIXME: many should be aliases to SCV's primitives for precision
  '(
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;;; 8.1 Data-structure Contracts
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    [flat-named-contract ; FIXME uses
     (any/c flat-contract? . -> . flat-contract?)]
    [any/c (any/c . -> . (not/c not))]
    [none/c (any/c . -> . not)]
    [ or/c (() #:rest (listof contract?) . ->* . contract?)]
    [and/c (() #:rest (listof contract?) . ->* . contract?)]
    [not/c (flat-contract? . -> . flat-contract?)]
    [=/c  (real? . -> . flat-contract?)]
    [</c  (real? . -> . flat-contract?)]
    [>/c  (real? . -> . flat-contract?)]
    [<=/c (real? . -> . flat-contract?)]
    [>=/c (real? . -> . flat-contract?)]
    [between/c (real? real? . -> . flat-contract?)]
    [#:alias real-in between/c]
    [integer-in (exact-integer? exact-integer? . -> . flat-contract?)]
    [char-in (char? char? . -> . flat-contract?)]
    [#:alias natural-number/c exact-nonnegative-integer?]
    [string-len/c (real? . -> . flat-contract?)]
    [#:alias false/c not]
    [#:pred printable/c]
    [one-of/c
     (() #:rest (listof flat-contract?) . ->* . contract?)]
    [symbols
     (() #:rest (listof symbol?) . ->* . flat-contract?)]
    [vectorof ; FIXME uses
     (contract? . -> . contract?)]
    [vector-immutableof (contract? . -> . contract?)]
    [vector/c ; FIXME uses
     (() #:rest (listof contract?) . ->* . contract?)]
    [vector-immutable/c
     (() #:rest (listof contract?) . ->* . contract?)]
    [box/c ; FIXME uses
     (contract? . -> . contract?)]
    [box-immutable/c (contract? . -> . contract?)]
    [listof (contract? . -> . list-contract?)]
    [non-empty-listof (contract? . -> . list-contract?)]
    [list*of (contract? . -> . contract?)]
    [cons/c (contract? contract? . -> . contract?)]
    [list/c
     (() #:rest (listof contract?) . ->* . list-contract?)]
    [syntax/c (flat-contract? . -> . flat-contract?)]
    [parameter/c ; FIXME uses
     (contract? . -> . contract?)]
    [procedure-arity-includes/c
     (exact-nonnegative-integer? . -> . flat-contract?)]
    [hash/c ; FIXME uses
     (chaperone-contract? contract? . -> . contract?)]
    [channel/c (contract? . -> . contract?)]
    [continuation-mark-key/c (contract? . -> . contract?)]
    [evt/c (() #:rest (listof chaperone-contract?) . ->* . chaperone-contract?)]
    [promise/c (contract? . -> . contract?)]
    [flat-contract ((any/c . -> . any/c) . -> . flat-contract?)]
    [flat-contract-predicate (flat-contract? . -> . (any/c . -> . any/c))]

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;;; 8.2 Function Contracts
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    [predicate/c contract?]
    [the-unsupplied-arg unsupplied-arg?]
    [#:pred unsupplied-arg?]


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;;; 8.8 Contract Utilities
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    [#:pred contract?]
    [#:pred chaperone-contract?]
    [#:pred impersonator-contract?]
    [#:pred flat-contract?]
    [#:pred list-contract?]
    [contract-name (contract? . -> . any/c)]
    [value-contract (has-contract? . -> . (or/c contract? not))]
    [#:pred has-contract?]
    [value-blame (has-blame? . -> . (or/c blame? not))]
    [#:pred has-blame?]
    [contract-projection (contract? . -> . (blame? . -> . (any/c . -> . any/c)))]
    [make-none/c (any/c . -> . contract?)]
    [contract-continuation-mark-key continuation-mark-key?]
    ))

(define prims.math
  '( 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;;; 1.2 Functions
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    [#:pred float-complex?]))

(define prims (append prims.04 prims.08 prims.math))


;; Declare implications between predicates.
;; Only need to do this for total predicates;
;; partial predicate like `even?` has a precondition of `integer?`,
;; and execution takes care of that.
;; Code generation should take care of transitivity, but redundancy is fine too.
;; TODO: reasonable to push this out to SMT solver?
(define implications
  '(; numbers
    [zero? ⇒ byte?]
    [byte? ⇒ fixnum?]
    [fixnum? ⇒ integer?]
    [integer? ⇒ rational?]
    [real? ⇒ number?]
    [float-complex? ⇒ number?]
    [not ⇒ boolean?]
    [exact-integer? ⇒ integer?]
    [exact-integer? ⇒ exact?]
    [exact-nonnegative-integer? ⇒ exact?]
    [#:exclusion exact-nonnegative-integer? negative?]
    [exact-nonnegative-integer? ⇒ integer?]
    [exact-positive-integer? ⇒ exact?]
    [exact-positive-integer? ⇒ positive?]
    [exact-positive-integer? ⇒ integer?]
    [inexact-real? ⇒ real?]
    [rational? ⇒ real?]
    [#:partition number? {exact? inexact?}]
    ; sequence
    [exact-nonnegative-integer? ⇒ sequence?]
    [string? ⇒ sequence?]
    [bytes ⇒ sequence?]
    [list? ⇒ sequence?]
    [vector? ⇒ sequence?]
    [flvector? ⇒ sequence?]
    [fxvector? ⇒ sequence?]
    [hash? ⇒ sequence?]
    [dict? ⇒ sequence?]
    [set? ⇒ sequence?]
    [input-port? ⇒ sequence?]
    [stream? ⇒ sequence?]
    ;; Sets
    [set-equal? ⇒ set?]
    [set-eqv? ⇒ set?]
    [set-eq? ⇒ set?]
    [set-mutable? ⇒ set?]
    [set-weak? ⇒ set?]
    ;; Arity
    [exact-nonnegative-integer? ⇒ procedure-arity?]

    [#:exclusion
     number? string? boolean? keyword? symbol?]
    ))


;; Experimental
;; Admitted evaluation result of standard functions
;; Probably won't scale...
(define evals
  '(
    [(map f xs)
     (null {(null? xs)})
     ((cons (f (car xs)) (map f (cdr xs))) {(cons? xs)})]
    [(list? xs)
     (#t {(null? xs)})
     ((list? (cdr xs)) {(cons? xs)})]
    ))

;; Check if `s` is a contract specifying a base value 
(define (base? s)
  (match s
    [(? symbol? s)
     (case s
       [(integer? real? number? exact-nonnegative-integer? flonum?
                  extflonum?
                  string? symbol? keyword? char? #|TODO|#)
        #t]
       [else #f])]
    [`(,(or 'and/c 'or/c 'not/c) ,cs ...)
     (andmap base? cs)]
    [_ #f]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-info?
  (match-λ? `(,(? symbol?) ,(? boolean?) ...)))

(define rng?
  (match-λ? ctc? `(values ,(? ctc?) ...)))

(define arr?
  (match-λ? `(,(? ctc?) ... . -> . ,(? rng?))))

(define arr*?
  (match-λ? `(,(? (listof ctc?)) #:rest ,(? ctc?) . ->* . ,(? rng?))))

(define ctc?
  (match-λ?
   (? symbol?)
   `(not/c ,(? symbol?))
   `(one-of/c ,(or (? number?) (? string?) `(quote ,(? symbol?)) (? boolean?)) ...)
   `(and/c ,(? ctc?) ...)
   `(or/c ,(? ctc?) ...)
   `(listof ,(? ctc?))
   `(list/c ,(? ctc?) ...)
   `(cons/c ,(? ctc?) ,(? ctc?))
   arr?
   arr*?))

(define dec?
  (match-λ?
   `(#:pred ,(? symbol?))
   `(#:pred ,(? symbol?) (,(? ctc?) ...))
   `(#:alias ,(? symbol?) ,(? symbol?))
   `(#:batch (,(? symbol?) ...) ,(? ctc?) ...)
   `(,(? symbol?) ,(? ctc?) ...)
   `(,(? symbol?) ,(? ctc?) ... #:other-errors ,(list (? ctc?) ...) ...)
   ;; struct stuff
   `(#:struct-cons ,(? symbol?) ,(? struct-info?))
   `(#:struct-pred ,(? symbol?) ,(? struct-info?))
   `(#:struct-acc  ,(? symbol?) ,(? struct-info?) ,(? exact-nonnegative-integer?))
   `(#:struct-mut  ,(? symbol?) ,(? struct-info?) ,(? exact-nonnegative-integer?))))

(define impl?
  (match-λ?
   `(,(? symbol?) ⇒ ,(? symbol?))
   `(#:partition ,(? symbol?) (,(? symbol?) ...))
   `(#:exclusion ,(? symbol?) ...)))
