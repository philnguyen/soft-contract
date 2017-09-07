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

(define-unit prims-04-04@
  (import prim-runtime^)
  (export)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.4 Byte Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; 4.4.1 Constructors, Selectors, Mutators
  (def-pred bytes?)
  (def make-bytes ; FIXME uses
    (exact-nonnegative-integer? byte? . -> . bytes?))
  (def bytes (() #:rest (listof byte?) . ->* . bytes?))
  (def bytes->immutable-bytes
    (bytes? . -> . (and/c bytes? immutable?)))
  (def-pred byte?)
  (def bytes-length (bytes? . -> . exact-nonnegative-integer?))
  (def bytes-ref (bytes? exact-nonnegative-integer? . -> . byte?))
  (def bytes-set! ((and/c bytes? (not/c immutable?)) exact-nonnegative-integer? byte? . -> . void?))
  (def subbytes
    (case->
     [bytes? exact-nonnegative-integer? . -> . bytes?]
     [bytes? exact-nonnegative-integer? exact-nonnegative-integer? . -> . bytes?]))
  (def bytes-copy
    (bytes? . -> . bytes?))
  (def bytes-copy!
    (case->
     [(and/c bytes? (not/c immutable?)) exact-nonnegative-integer? bytes? . -> . void?]
     [(and/c bytes? (not/c immutable?)) exact-nonnegative-integer? bytes? exact-nonnegative-integer? . -> . void?]
     [(and/c bytes? (not/c immutable?)) exact-nonnegative-integer? bytes? exact-nonnegative-integer? exact-nonnegative-integer? . -> . void?]))
  (def bytes-fill!
    ((and/c bytes? (not/c immutable?)) byte? . -> . void?))
  (def bytes-append (() #:rest (listof bytes?) . ->* . bytes?))
  (def bytes->list (bytes? . -> . (listof byte?)))
  (def list->bytes ((listof byte?) . -> . bytes?))
  (def make-shared-bytes
    (case->
     [exact-nonnegative-integer? . -> . bytes?]
     [exact-nonnegative-integer? byte? . -> . bytes?]))
  (def shared-bytes (() #:rest (listof byte?) . ->* . bytes?))

  ;; 4.4.2 Byte String Comparisons
  ; FIXME varargs
  (def-preds (bytes=? bytes<? bytes>?) (bytes? bytes?))

  ;; 4.4.3 Bytes to/from Characers, Decoding and Encoding
  (def* (bytes->string/utf-8 bytes->string/locale bytes->string/latin-1)
    (case->
     [bytes? . -> . string?]
     [bytes? (or/c not char?) . -> . string?]
     [bytes? (or/c not char?) exact-nonnegative-integer? . -> . string?]
     [bytes? (or/c not char?) exact-nonnegative-integer? exact-nonnegative-integer? . -> . string?]))
  (def* (string->bytes/utf-8 string->bytes/locale string->bytes/latin-1)
    (case->
     [string? . -> . bytes?]
     [string? (or/c not byte?) . -> . bytes?]
     [string? (or/c not byte?) exact-nonnegative-integer? . -> . bytes?]
     [string? (or/c not byte?) exact-nonnegative-integer? exact-nonnegative-integer? . -> . bytes?]))
  (def string-utf-8-length
    (case->
     [string? . -> . exact-nonnegative-integer?]
     [string? exact-nonnegative-integer? . -> . exact-nonnegative-integer?]
     [string? exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?]))
  (def bytes-utf-8-length
    (case->
     [bytes? . -> . exact-nonnegative-integer?]
     [bytes? (or/c not char?) . -> . exact-nonnegative-integer?]
     [bytes? (or/c not char?) exact-nonnegative-integer? . -> . exact-nonnegative-integer?]
     [bytes? (or/c not char?) exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer?]))
  (def* (bytes-utf-8-ref bytes-utf-8-index)
    (case->
     [bytes? . -> . (or/c not char?)]
     [bytes? exact-nonnegative-integer?  . -> . (or/c not char?)]
     [bytes? exact-nonnegative-integer? (or/c not char?) . -> . (or/c not char?)]
     [bytes? exact-nonnegative-integer? (or/c not char?) exact-nonnegative-integer? . -> . (or/c not char?)]
     [bytes? exact-nonnegative-integer? (or/c not char?) exact-nonnegative-integer? exact-nonnegative-integer? . -> . (or/c not char?)]))

  ;; 4.4.4 Bytes to Bytes Encoding Conversion
  (def bytes-open-converter (string? string? . -> . (or/c bytes-converter? not)))
  (def bytes-close-converter (bytes-converter? . -> . void?))
  #;[bytes-convert FIXME
                   (bytes-converter? bytes? . -> . any/c)]
  #;[bytes-convert-end]
  (def-pred bytes-converter?)
  (def locale-string-encoding (-> any/c))

  ;; 4.4.5 Additional Byte String Functions
  #;[bytes-append*]
  (def bytes-join ((listof bytes?) bytes? . -> . bytes?))
  
  )
