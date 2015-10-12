#lang racket/base
(require racket/contract "untyped-macros.rkt")
(provide
 dec? impl?
 (contract-out
  [prims (listof dec?)]
  [implications (listof impl?)]))

;; FIXME annotation for side effects

(define prims
  '[;; Total predicates

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

     [#:const true]
     [#:const false]
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
     [/ ; FIXME varargs, only error on exact 0
      (number? (and/c number? (not/c zero?)) . -> . number?)
      (real? real? . -> . real?)]
     [#:batch (quotient remainder modulo) ; FIXME: only error on exact 0
      (integer? (and/c integer? (not/c zero?)) . -> . integer?)]
     #;[quotient/remainder
      (integer? (and/c integer? (not/c zero?))) . -> . integer? integer?] ; FIXME
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
     [random ; FIXME range, all usages
      (integer? . -> . exact-nonnegative-integer?)]
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
     [number->string ; FIXME usages
      (number? . -> . string?)]
     [string->number ; FIXME usages
      (string? . -> . (or/c number? not))]
     [real->decimal-string ; FIXME usages
      (real? exact-nonnegative-integer? . -> . string?)]
     [integer-bytes->integer ; FIXME usages
      (bytes? any/c . -> . exact-integer?)]
     [integer->integer-bytes ; FIXME usages
      (exact-integer? (one-of/c 2 4 8) any/c . -> . bytes?)]
     [floating-point-bytes->real ; FIXME usages
      (bytes . -> . flonum?)]
     [real->floating-point-bytes ; FIXME usages
      (real? (one-of/c 2 4 8) . -> . bytes?)]
     [system-big-endian? ; FIXME: opaque or machine dependent? (former probably)
      (-> boolean?)]

     ;; 4.2.2.10 Extra Functions
     [#:const pi]
     [#:const pi.f]
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
      (number? . -> . flonum?)]
     [flrandom ; FIXME range
      (pseudo-random-generator? . -> . flonum?)]

     ;; 4.2.3.2 Flonum Vectors
     [#:pred flvector?]
     #;[flvector
        (-> flvector?)]
     [make-flvector ; FIXME usages
      (exact-nonnegative-integer? flonum? . -> . flvector?)]
     [flvector-length
      (flvector? . -> . exact-nonnegative-integer?)]
     [flvector-ref
      (flvector? exact-nonnegative-integer? . -> . flonum?)]
     [flvector-set!
      (flvector? exact-nonnegative-integer? flonum? . -> . flonum?)]
     [flvector-copy ; FIXME usages
      (flvector? . -> . flvector?)]
     [in-flvector ; FIXME usages
      (flvector? . -> . sequence?)]
     #;[shared-flvector
      (-> flvector?)]
     [make-shared-flvector ; FIXME usages
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
     [make-fxvector ; FIXME usages
      (exact-nonnegative-integer? fixnum? . -> . fxvector?)]
     [fxvector-length
      (fxvector? . -> . exact-nonnegative-integer?)]
     [fxvector-ref
      (fxvector? exact-nonnegative-integer? . -> . fixnum?)]
     [fxvector-set!
      (fxvector? exact-nonnegative-integer? fixnum? . -> . fixnum?)]
     [fxvector-copy ; FIXME usages
      (fxvector? . -> . fxvector?)]
     [in-fxvector ; FIXME usages
      (fxvector? . -> . sequence?)]
     #;[shared-fxvector
      (-> fxvector?)]
     [make-shared-fxvector ; FIXME usages
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
     [#:batch (extflsin extflcos extfltan extflasin extflacons extflatan
               extfllog extflexp extflsqrt)
      (extflonum? . -> . extflonum?)]
     [extflexpt
      (extflonum? extflonum? . -> . extflonum?)]
     [->extfl
      (exact-integer? . -> . extflonum?)]
     [extfl->exact-integer
      (extflonum? . -> . exact-integer?)]
     [real->extfl
      (real? . -> . extfl)]
     [extfl->exact
      (real? . -> . (and/c real? exact?))]
     [extfl->inexact
      (real? . -> . flonum?)]

     ;; 4.2.5.2 Extflonum Constants
     [#:const pi.t]
     
     ;; 4.2.5.3 Extflonum Vectors
     [#:pred extflvector?]
     #;[extflvector
      (-> extflvector?)]
     [make-extflvector ; FIXME usages
      (exact-nonnegative-integer? extflonum? . -> . extflvector?)]
     [extflvector-length
      (extflvector? . -> . exact-nonnegative-integer?)]
     [extflvector-ref
      (extflvector? exact-nonnegative-integer? . -> . extflonum?)]
     [extflvector-set!
      (extflvector? exact-nonnegative-integer? extflonum? . -> . extflonum?)]
     [extflvector-copy ; FIXME usages
      (extflvector? . -> . extflvector?)]
     [in-extflvector
      (extflvector? . -> . sequence?)]
     [make-shared-extflvector
      (exact-nonnegative-integer? . -> . extflvector?)]

     ;; 4.2.5.4 Extflonum Byte Strings
     [floating-point-bytes->extfl ; FIXME usages
      (bytes . -> . extflonum?)]
     [extfl->floating-point-bytes
      (extflonum? . -> . bytes?)]
     

     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.3 Strings
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     
     
     ;; 4.3.1 Constructors, Selectors, Mutators
     [#:pred string?]
     [make-string ; FIXME all usages
      (exact-nonnegative-integer? char? . -> . string?)]
     #;[string ; FIXME varargs
      (() #:rest char? →* string?)]
     [string->immutable-string
      (string? . -> . (and/c string? immutable?))]
     [string-length
      (string? . -> . exact-nonnegative-integer?)]
     [string-ref
      (string? exact-nonnegative-integer? . -> . char?)]
     [string-set!
      ((and/c string? (not/c immutable?)) exact-nonnegative-integer? char? . -> . void?)]
     [substring ; FIXME usages
      (string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?)]
     [string-copy
      (string . -> . string?)]
     [string-copy! ; FIXME usages
      ((and/c string? (not/c immutable?)) exact-nonnegative-integer? string? . -> . void?)]
     [string-fill! ; FIXME usages
      ((and/c string? (not/c immutable?)) char? . -> . void?)]
     [string-append ; FIXME varargs
      (string? string? . -> . string?)]
     [string->list
      (string? . -> . (listof char?))]
     [list->string
      ((listof char?) . -> . string?)]
     [build-string
      (exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?)]
     
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
               string-locale-ci=? string-locale-ci<? string-locale-ci>?
               string-locale-upcase string-locale-downcase)
      (string? . -> . string?)]

     ;; 4.3.5 Additional String Functions
     #;[string-append* #;FIXME]
     [string-join ; FIXME usages
      ((listof string?) . -> . string?)]
     [string-normalize-spaces ; FIXME usages
      (string? . -> . string?)]
     [string-replace ; FIXME usages
      (string? (or/c string? regexp?) string? . -> . string?)]
     [string-split ; FIXME usages
      (string? . -> . (listof string?))]
     [string-trim ; FIXME usages
      (string? . -> . string?)]
     [#:pred non-empty-string?]
     [#:batch (string-contains? string-prefix? string-suffix?)
      (string? string? . -> . boolean?)]

     ;; 4.3.6 Converting Values to Strings.
     [#:batch (~a ~v ~s ~e ~r ~.a ~.v ~.s) ; FIXME usages
      (any/c . -> . string?)]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.4 Byte Strings
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; 4.4.1 Constructors, Selectors, Mutators
     [#:pred bytes?]
     [make-bytes ; FIXME usages
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
     [subbytes ; FIXME usages
      bytes? exact-nonnegative-integer? . -> . bytes?]
     [bytes-copy
      (bytes? . -> . bytes?)]
     [bytes-copy! ; FIXME usages
      ((and/c bytes? (not/c immutable?)) exact-nonnegative-integer? bytes? . -> . void?)]
     [bytes-fill!
      ((and/c bytes? (not/c immutable?)) byte? . -> . void?)]
     [bytes-append ; FIXME varargs
      (bytes? bytes? . -> . bytes?)]
     [bytes->list
      (bytes? . -> . (listof byte?))]
     [list->bytes
      ((listof byte?) . -> . bytes?)]
     [make-shared-bytes ; FIXME usages
      (exact-nonnegative-integer? byte? . -> . bytes?)]
     #;[shared-bytes
      (-> bytes)]

     ;; 4.4.2 Byte String Comparisons
     ; FIXME varargs
     [#:batch (bytes=? bytes<? bytes>?)
      (bytes? bytes? . -> . boolean?)]
     
     ;; 4.4.3 Bytes to/from Characers, Decoding and Encoding
     ; FIXME usages
     [#:batch (bytes->string/utf-8 bytes->string/locale bytes->string/latin-1)
      (bytes? . -> . string?)]
     [#:batch (string->bytes/utf-8 string->bytes/locale string->bytes/latin-1)
      (string? . -> . bytes?)]
     [string-utf-8-length ; FIXME usages
      (string? . -> . exact-nonnegative-integer?)]
     [bytes-utf-8-length ; FIXME usages
      (bytes? . -> . exact-nonnegative-integer?)]
     [#:batch (bytes-utf-8-ref bytes-utf-8-index) ; FIXME usages
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
     [gensym ; FIXME usage
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
     [regexp-quote ; FIXME usages
      ((or/c string? bytes?) . -> . (or/c string? bytes?))
      (string? . -> . string?)
      (bytes? . -> . bytes?)]
     [regexp-max-lookbehind
      (exact-nonnegative-integer? . -> . (or/c regexp? byte-regexp?))]

     ;; 4.7.4 Regexp Matching
     [regexp-match ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match* ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-try-match ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match-positions ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match-positions* ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       any/c)]
     [regexp-match? ; FIXME usages
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path? input-port?)
       . -> .
       boolean?)]
     [regexp-match-exact? ; FIXME usages
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? path?)
       . -> .
       boolean?)]
     [regexp-match-peek ; FIXME usages
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c bytes? (listof (or/c bytes? not)))))]
     [regexp-match-peek-positions ; FIXME usages
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c (cons/c exact-nonnegative-integer?
                             exact-nonnegative-integer?)
                     (listof (or/c (cons/c exact-nonnegative-integer?
                                           exact-nonnegative-integer?)
                                   not)))
             not))]
     [regexp-match-peek-immediate ; FIXME usages
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c bytes? (listof (or/c bytes? not)))
             not))]
     [regexp-match-peek-positions-immediate ; FIXME usages
      ((or/c string? bytes? regexp? byte-regexp?)
       input-port?
       . -> .
       (or/c (cons/c (cons/c exact-nonnegative-integer?
                             exact-nonnegative-integer?)
                     (listof (or/c (cons/c exact-nonnegative-integer?
                                           exact-nonnegative-integer?)
                                   not)))
             not))]
     [regexp-match-peek-positions* ; FIXME usages, precision
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
     #;[regexp-match-positions/end ; FIXME usages
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
     [regexp-split ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes? input-port?)
       . -> .
       any/c)]

     ;; 4.7.6 Regexp Substitution
     [regexp-replace ; FIXME usages, precision
      ((or/c string? bytes? regexp? byte-regexp?)
       (or/c string? bytes?)
       (or/c string? bytes? #|TODO more|#)
       . -> .
       any/c)]
     [regexp-replace* ; FIXME usages
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
     ;[#:pred pair?]
     ;[#:pred null?]
     #;[cons
      (any/c any/c . -> . pair?)]
     #;[car
      (pair? . -> . any/c)]
     #;[cdr
      (pair? . -> . any/c)]
     ;[#:const null]
     ;[#:pred list?]
     ; TODO
     


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.10 Mutable Pairs and Lists
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.11 Vectors
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.12 Boxes
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.13 Hash Tables
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.14 Sequences and Streams
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;;;;; 4.14.1 Sequences

     ;; 4.14.1.1 Predicate and Constructors
     [#:pred sequence?]
     ; TODO


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.15 Dictionaries
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.16 Sets
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.17 Procedures
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO
     [#:pred procedure?]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.18 Void
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:pred void?]
     [void ; FIXME varargs
      (-> void?)]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.19 Undefined
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     [#:const undefined]
])

(define impl?
  (match-λ?
   `(,(? symbol?) ⇒ ,(? ctc?))
   `(#:partition ,(? symbol?) (,(? symbol?) ...))))

;; Declare implications between predicates.
;; Only need to do this for total predicates;
;; partial predicate like `even?` has a precondition of `integer?`,
;; and execution takes care of that.
;; Code generation should take care of transitivity, but redundancy is fine too.
(define implications
  '(; numbers
    [zero? ⇒ byte?]
    [byte? ⇒ fixnum?]
    [fixnum? ⇒ integer?]
    [integer? ⇒ rational?]
    [real? ⇒ number?]
    [not ⇒ boolean?]
    [exact-integer? ⇒ integer?]
    [exact-integer? ⇒ exact?]
    [exact-nonnegative-integer? ⇒ exact?]
    [exact-nonnegative-integer? ⇒ (not/c negative?)]
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
    ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ctc?
  (match-λ?
   (? symbol?)
   `(not/c ,(? symbol?))
   `(one-of/c ,(or (? number?) (? string?) (? symbol?) (? boolean?)) ...)
   `(and/c ,(? ctc?) ...)
   `(or/c ,(? ctc?) ...)
   `(listof ,(? ctc?))
   `(list/c ,(? ctc?) ...)
   `(cons/c ,(? ctc?) ,(? ctc?))
   `(,(? ctc?) ... . -> . ,(? ctc?))))

(define dec?
  (match-λ?
   `(#:const ,(? symbol?))
   `(#:pred ,(? symbol?))
   `(#:pred ,(? symbol?) (,(? ctc?) ...))
   `(#:alias ,(? symbol?) ,(? symbol?))
   `(#:batch (,(? symbol?) ...) ,(? ctc?) ...)
   `(,(? symbol?) ,(? ctc?) ...)
   `(,(? symbol?) ,(? ctc?) ... #:other-errors ,(list (? ctc?) ...) ...)))
