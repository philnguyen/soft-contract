#lang typed/racket/base

(provide prims-04-03@)

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
         racket/generator
         racket/random
         racket/format
         racket/splicing
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
;;;;; 4.3 Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-03@
  (import prim-runtime^)
  (export)

  ;; 4.3.1 Constructors, Selectors, Mutators
  (def-pred string?)
  (def make-string
    (case->
     (exact-nonnegative-integer? . -> . string?) ; TODO: "stringof..."?
     (exact-nonnegative-integer? char? . -> . (and/c string? (not/c immutable?)))))
  (def string (() #:rest (listof char?) . ->* . string?))
  (def string->immutable-string
    (string? . -> . (and/c string? immutable?)))
  (def string-length
    (string? . -> . exact-nonnegative-integer?))
  (def string-ref (string? exact-nonnegative-integer? . -> . char?))
  (def string-set!
    ((and/c string? (not/c immutable?)) exact-nonnegative-integer? char? . -> . void?))
  (def substring
    (case->
     [string? exact-nonnegative-integer? . -> . string?]
     [string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?]))
  (def string-copy (string? . -> . string?))
  (def string-copy!
    (case->
     [(and/c string? (not/c immutable?)) exact-nonnegative-integer? string? . -> . void?]
     [(and/c string? (not/c immutable?)) exact-nonnegative-integer? string? exact-nonnegative-integer? . -> . void?]
     [(and/c string? (not/c immutable?)) exact-nonnegative-integer? string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . void?]))
  (def string-fill! ((and/c string? (not/c immutable?)) char? . -> . void?))
  (def string-append (() #:rest (listof string?) . ->* . string?)
    #:refinements
    (() #:rest (listof path-string?) . ->* . path-string?))
  (def string->list (string? . -> . (listof char?))
    #:refinements
    (non-empty-string? . -> . pair?)
    ((not/c non-empty-string?) . -> . null?))
  (def list->string ((listof char?) . -> . string?))
  (def build-string
    (exact-nonnegative-integer? (exact-nonnegative-integer? . -> . char?) . -> . string?))

  ;; 4.3.2 String Comparisons. FIXME varargs
  (def-preds (string=? string<? string<=? string>? string>=?
                       string-ci=? string-ci<? string-ci<=? string-ci>? string-ci>=?)
    (string? string?))

  ;; 4.3.3 String Conversions
  (def* (string-upcase string-downcase string-titlecase string-foldcase
                            string-normalize-nfd string-normalize-nfkd
                            string-normalize-nfc string-normalize-nfkc)
    (string? . -> . string?))

  ;; 4.3.4 Locale-specific string operations 
  ; FIXME varargs
  (def* (string-locale=? string-locale<? string-locale>?
                              string-locale-ci=? string-locale-ci<? string-locale-ci>?)
    (string? string? . -> . string?))
  (def* (string-locale-upcase string-locale-downcase)
    (string? . -> . string?))

  ;; 4.3.5 Additional String Functions
  #;[string-append* #;FIXME]
  (def string-join ; FIXME uses, keywords
    (case->
     [(listof string?) . -> . string?]
     [(listof string?) string? . -> . string?]))
  (def string-normalize-spaces ; FIXME keywords
    (string? . -> . string?))
  (def string-replace ; FIXME keywords
    (string? (or/c string? regexp?) string? . -> . string?))
  (def string-split ; FIXME keywords
    (case->
     [string? . -> . (listof string?)]
     [string? (or/c string? regexp?) . -> . (listof string?)]))
  (def string-trim ; FIXME keywords
    (case->
     [string? . -> . string?]
     [string? (or/c string? regexp?) . -> . string?]))
  (def-pred non-empty-string?)
  (def-preds (string-contains? string-prefix? string-suffix?) (string? string?))

  ;; 4.3.6 Converting Values to Strings.
  (def* (~a ~v ~s ~e ~.a ~.v ~.s) (∀/c (_) (_ . -> . string?))) ; FIXME keywords
  (def ~r (rational? . -> . string?)) ; FIXME keywords
  )
