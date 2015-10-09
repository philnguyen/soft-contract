#lang racket/base
(require racket/math racket/contract)
(provide prims)

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
     [#:batch (gcd lcm) ; FIXME varargs, `rational?`
      (integer? integer? → integer?)]
     [#:batch (round floor ceiling truncate)
      (real? → real?)]
     [#:batch (numerator denominator) ; FIXME `rational?`
      (integer? → integer?)]
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
     [#:batch (bitwise-ior bitwise-and bitwise-xor) ; FIXME varargs, `exact-integer?`
      (integer? integer? → integer?)]
     [bitwise-not ; FIXME `exact-integer?`
      (integer? → integer?)]
     [bitwise-bit-set? ; FIXME `exact?`
      (integer? (and/c integer? (not/c negative?)) → boolean?)]
     [bitwise-bit-field ; FIXME `exact?`, `start ≤ end`
      (integer? (and/c integer? (not/c negative?)) (and/c integer? (not/c negative?)) → integer?)]
     [arithmetic-shift ; FIXME exact
      (integer? integer? → integer?)]
     [integer-length ; FIXME exact
      (integer? → integer?)]

     ;; 4.2.2.7 Random Numbers
     [random ; FIXME range, exact?, all usages
      (integer? → integer?)]
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
     [#:batch (exact-round exact-floor exact-ceiling exact-truncate) ; FIXME exact
      (real? → integer?)]
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
     [make-string ; FIXME exact, all usages
      ((and/c integer? (not/c negative?)) char? → string?)]
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
     ;;;;; Misc
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     
     [#:pred string?]
     [#:pred symbol?]
     [#:pred procedure?]
     [#:pred keyword?]
     [#:pred char?]
     [#:pred regexp?]
))

;; Declare implications between predicates.
;; Only need to do this for total predicates;
;; partial predicate like `even?` has a precondition of `integer?`,
;; and execution takes care of that.
;; Code generation should take care of transitivity, but redundancy is fine too.
(define inferences
  #'([integer? ⇒ real?]
     [real? ⇒ number?]
     [not ⇒ boolean?]
     [exact? inexact? ⇒ number?]
     [exact-integer? exact-nonnegative-integer? exact-positive-integer? ⇒ integer? exact?]
     [exact-nonnegative-integer? ⇒ (not/c negative?)]
     [exact-positive-integer? ⇒ positive?]
     [inexact-real? ⇒ real?]
     ;; exclusions
     ))
