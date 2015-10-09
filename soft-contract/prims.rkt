#lang racket/base
(require racket/match racket/math racket/contract racket/set
         "untyped-macros.rkt" "utils.rkt")
(provide prims implications)

;; FIXME annotation for side effects

(define prims
  #'(;; Total predicates

     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.1 Booleans and Equality
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     [#:pred boolean?]
     [#:pred not]
     [#:alias false? not]
     [#:pred equal? (any/c any/c)]
     ;[#:pred eqv? (any/c any/c)]
     ;[#:pred eq? (any/c any/c)]
     ;[#:pred equal?/recur (any/c any/c (any/c any/c → any/c) → any/c)]
     [#:pred immutable?]
     [#:pred symbol=? (symbol? symbol?)]
     [#:pred boolean=? (boolean? boolean?)]
     [xor
      (any/c any/c → any/c)]

     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.2 Numbers
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;;;;; 4.2.1 Number Types
     [#:pred number?]
     [#:alias complex? number?]
     [#:pred real?]
     [#:pred integer?]
     [#:pred rational?]
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
      (number? → exact?)]
     [exact->inexact
      (number? → inexact?)]
     [real->single-flonum
      (real? → single-flonum?)]
     [real->double-flonum
      (real? → flonum?)]
     
     ;;;;; 4.2.2 Generic Numerics
     
     ;; 4.2.2.1 Arithmetic
     [#:batch (+ - *) ; FIXME var-args
      (number? number? → number?)
      (real? real? → real?)
      (integer? integer? → integer?)]
     [/ ; FIXME varargs
      (number? (and/c number? (not/c zero?)) → number?)
      (real? real? → real?)]
     [#:batch (quotient remainder modulo)
      (integer? (and/c integer? (not/c zero?)) → integer?)]
     #;[quotient/remainder
      (integer? (and/c integer? (not/c zero?))) → integer? integer?] ; FIXME
     [#:batch (add1 sub1)
      (number? → number?)
      (real? → real?)
      (integer? → integer?)]
     [abs
      (real? → real?)
      (integer? → integer?)]
     [#:batch (max min) ; FIXME varargs
      (real? real? → real?)
      (integer? integer? → integer?)]
     [#:batch (gcd lcm) ; FIXME varargs
      (rational? rational? → rational?)]
     [#:batch (round floor ceiling truncate)
      (real? → real?)]
     [#:batch (numerator denominator)
      (rational? → integer?)]
     [rationalize
      (real? real? → real?)]

     ;; 4.2.2.2 Number Comparison
     [#:pred = (number? number?)] ; FIXME varargs
     [#:pred < (real? real?)]
     [#:pred <= (real? real?)]
     [#:pred > (real? real?)]
     [#:pred >= (real? real?)]

     ;; 4.2.2.3 Powers and Roots
     [sqrt
      (number? → number?)
      (real? → real?)]
     [integer-sqrt
      (integer? → number?)
      (real? → real?)]
     #;[integer-sqrt/remainder ; FIXME
      (integer? → number? integer?)]
     [expt
      (number? number? → number?)
      (real? real? → real?)
      #:other-errors
      (zero? negative?)]
     [exp
      (number? → number?)]
     [log
      (number? → number?)]

     ;; 4.2.2.4 Trigonometric Functions
     [#:batch (log sin cos tan asin acos atan)
      (number? → number?)
      (real? → real?)]

     ;; 4.2.2.5 Complex Numbers
     [#:batch (make-rectangular make-polar)
      (real? real? → number?)]
     [#:batch (real-part imag-part)
      (number? → real?)]
     [magnitude
      (number? → (and/c real? (not/c negative?)))]
     [angle
      (number? → real?)]

     ;; 4.2.2.6 Bitwise Operations
     [#:batch (bitwise-ior bitwise-and bitwise-xor) ; FIXME varargs
      (exact-integer? exact-integer? → exact-integer?)]
     [bitwise-not
      (exact-integer? → exact-integer?)]
     [bitwise-bit-set?
      (exact-integer? exact-nonnegative-integer? → boolean?)]
     [bitwise-bit-field ; FIXME `start ≤ end`
      (exact-integer? exact-nonnegative-integer? exact-nonnegative-integer? → integer?)]
     [arithmetic-shift
      (exact-integer? exact-integer? → exact-integer?)]
     [integer-length ; TODO post-con more precise than doc. Confirm.
      (exact-integer? → exact-nonnegative-integer?)]

     ;; 4.2.2.7 Random Numbers
     [random ; FIXME range, all usages
      (integer? → exact-nonnegative-integer?)]
     [random-seed
      (integer? → void?)]
     [make-pseudo-random-generator
      (→ pseudo-random-generator?)]
     [#:pred pseudo-random-generator?]
     [current-pseudo-random-generator ; FIXME parameter
      (→ pseudo-random-generator?)]
     ; FIXME rest

     ;; 4.2.2.8 System-Provided Randomness
     ; FIXME

     ;; 4.2.2.9 Number-String Conversions
     [number->string
      (number? → string?)]
     [string->number
      (string? → (or/c number? not))]
     [real->decimal-string
      (real? (and/c integer? (not/c negative?)) → string?)]
     ; FIXME rest, `bytes?`
     [system-big-endian?
      (→ boolean?)]

     ;; 4.2.2.10 Extra Functions
     [#:batch (degrees->radians radians->degrees)
      (real? → real?)]
     [sqr
      (number? → number?)
      (real? → real?)
      (integer? → integer?)]
     [sgn ; FIXME precise
      (real? → real?)]
     [conjugate
      (number? → number?)]
     [#:batch (sinh cosh tanh)
      (number? → number?)]
     [#:batch (exact-round exact-floor exact-ceiling exact-truncate)
      (rational? → exact-integer?)]
     [order-of-magnitude
      ((and/c real? positive?) → integer?)]
     [nan?
      (real? → boolean?)]
     [infinite?
      (real? → boolean?)]


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.3 Strings
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     
     
     ;; 4.3.1 Constructors, Selectors, Mutators
     [#:pred string?]
     [make-string ; FIXME all usages
      (exact-nonnegative-integer? char? → string?)]
     #;[string ; FIXME varargs
      (() #:rest char? →* string?)]
     [string->immutable-string
      (string? → string?)]
     [string-length
      (string? → integer?)
      (string? → (not/c negative?))]
     [string-ref
      (string? (and/c integer? (not/c negative?)) → char?)]
     #;[string-set! ; FIXME mutable
      ((and/c string? (not/c immutable?)) integer? char? → void?)]
     [substring
      (string? (and/c integer? (not/c negative?)) (and/c integer? (not/c negative?)) → string?)]
     [string-copy
      (string → string?)]
     #;[string-copy!] ; FIXME
     #;[string-fill!] ; FIXME
     [string-append ; FIXME varargs
      (string? string? → string?)]
     #;[string->list
      (string? → (listof char?))]
     [list->string
      ((listof char?) → string?)]
     [build-string
      ((and/c integer? (not/c negative?)) ((and/c integer? (not/c negative?)) → string?))]
     
     ;; 4.3.2 String Comparisons. FIXME varargs
     [#:batch (string=? string<? string<=? string>? string>=?
               string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?)
      (string? string? → boolean?)]

     ;; 4.3.3 String Conversions
     [#:batch (string-upcase string-downcase string-titlecase string-foldcase
               string-normalize-nfd string-normalize-nfkd string-normalize-nfc string-normalize-nfkc)
      (string? → string?)]

     ;; 4.3.4 Locale-specific string operations 
     ; FIXME varargs
     [#:batch (string-locale=? string-locale<? string-locale>?
               string-locale-ci=? string-locale-ci<? string-locale-ci>?
               string-locale-upcase string-locale-downcase)
      (string? → string?)]

     ;; 4.3.5 Additional String Functions
     #;[string-append* #;FIXME]
     #;[string-join
      ((listof string?) → string?)]
     [string-normalize-spaces ; FIXME usages
      (string? → string?)]
     [string-replace ; FIXME usages
      (string? (or/c string? regexp?) string? → string?)]
     #;[string-split ; FIXME usages
      (string? → (listof string?))]
     [string-trim ; FIXME usages
      (string? → string?)]
     [non-empty-string?
      (any/c → boolean?)]
     [#:batch (string-contains? string-prefix? string-suffix?)
      (string? string? → boolean?)]

     ;; 4.3.6 Converting Values to Strings. TODO


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.4 Byte Strings
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ; TODO

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.5 Characters
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     ;; 4.5.1 Characters and Scalar Values

     [#:pred char?]
     [char->integer
      (char? → exact-integer?)]
     [integer->char ; FIXME range
      (exact-integer? → char?)]
     [char-utf-8-length ; FIXME range
      (char? → exact-integer?)]
     
     ;; 4.5.2 Comparisons
     [#:batch (char=? char<? char<=? char>? char>=?
               char-ci=? char-ci<? char-ci<=? char-ci>? char-ci>=?) ; FIXME varargs
      (char? char? → boolean?)]
     
     ;; 4.5.3 Classifications
     [#:batch (char-alphabetic? char-lower-case? char-upper-case? char-title-case?
               char-numeric? char-symbolic? char-punctuation? char-graphic?
               char-whitespace? char-blank? char-iso-control? char-general-category)
      (char? → boolean?)]
     #;[make-known-char-range-list
      (→ (listof (list/c exact-nonnegative-integer?
                         exact-nonnegative-integer?
                         boolean?)))]

     ;; 4.5.4 Character Conversions
     [#:batch (char-upcase char-downcase char-titlecase char-foldcase)
      (char? → char?)]
     
     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.6 Symbols
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     [#:pred symbol?]
     [#:pred symbol-interned? (symbol?)]
     [#:pred symbol-unreadable? (symbol?)]
     [symbol->string
      (symbol? → string?)]
     [#:batch (string->symbol string->uninterned-symbol string->unreadable-symbol)
      (string? → symbol?)]
     [gensym ; FIXME usage
      (→ symbol?)]
     [#:pred symbol<? (symbol? symbol?)] ; FIXME varargs


     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.7 Regular Expressions
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO
     [#:pred regexp?]



     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.8 Keywords
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; TODO
     [#:pred keyword?]


     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.9 Pairs and Lists
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
      (→ void?)]

     
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;;;; 4.19 Undefined
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ; Nothing for now
))



;; Declare implications between predicates.
;; Only need to do this for total predicates;
;; partial predicate like `even?` has a precondition of `integer?`,
;; and execution takes care of that.
;; Code generation should take care of transitivity, but redundancy is fine too.
(define implications
  '([zero? ⇒ integer?]
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
    ))
