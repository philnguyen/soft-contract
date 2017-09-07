#lang typed/racket/base

(provide prims-04-05@)

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
;;;;; 4.5 Characters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-05@
  (import prim-runtime^)
  (export)

  ;; 4.5.1 Characters and Scalar Values

  (def-pred char?)
  (def char->integer (char? . -> . exact-integer?))
  (def integer->char
    ((and/c exact-integer?
            (or/c (and/c (>=/c 0) (<=/c 55295))
                  (and/c (>=/c 57344) (<=/c 1114111)))) . -> . char?))
  (def char-utf-8-length (char? . -> . (and/c exact-integer? (>=/c 1) (<=/c 6))))

  ;; 4.5.2 Comparisons
  (def* (char=? char<? char<=? char>? char>=?
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
  (def* (char-upcase char-downcase char-titlecase char-foldcase)
    (char? . -> . char?))
  
  )
