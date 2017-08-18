#lang typed/racket/base

(provide prims-04-04@)

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
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-04-04@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^)
  (export)

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
  
  )
