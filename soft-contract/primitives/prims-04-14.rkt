#lang typed/racket/base

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

(provide prims-04-14@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.14 Sequences and Streams
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-14@
  (import prim-runtime^)
  (export)

  ;;;;; 4.14.1 Sequences

  ;; 4.14.1.1 Predicate and Constructors
  (def-pred sequence?)
  (def in-range ; FIXME uses
    (real? real? real? . -> . stream?))
  (def in-naturals ; FIXME uses
    (exact-nonnegative-integer? . -> . stream?))
  (def in-list
    (list? . -> . stream?))
  #;[in-mlist ; FIXME don't know about `mlist?`
     (mlist? . -> . stream?)]
  (def in-vector ; FIXME uses
    (vector? . -> . sequence?))
  (def in-string ; FIXME uses
    (string? . -> . sequence?))
  (def in-bytes ; FIXME uses
    (bytes? . -> . sequence?))
  (def in-port ; FIXME uses
    ((input-port? . -> . any/c) input-port? . -> . sequence?))
  (def in-input-port-bytes
    (input-port? . -> . sequence?))
  (def in-input-port-chars
    (input-port? . -> . sequence?))
  (def in-lines ; FIXME uses
    (input-port? (or/c 'linefeed 'return 'return-linefeed 'any 'any-one)
                 . -> . sequence?))
  (def in-bytes-lines ; FIXME uses
    (input-port? (or/c 'linefeed 'return 'return-linefeed 'any 'any-one)
                 . -> . sequence?))
  (def in-hash
    (hash? . -> . sequence?))
  (def* (in-hash-keys in-hash-values)
    (hash? . -> . sequence?))
  (def in-hash-pairs
    (hash? . -> . sequence?))
  (def in-directory ; FIXME uses
    ((or/c path-string? not) . -> . sequence?))
  (def in-producer ; FIXME uses
    (procedure? . -> . sequence?))
  (def in-value
    (any/c . -> . sequence?))
  (def in-indexed
    (sequence? . -> . sequence?))
  #;[in-sequences ; FIXME listof
     (() #:rest (listof sequence?) . ->* . sequence?)]
  #;[in-cycle ; FIXME listof
     (() #:rest (listof sequence?) . ->* . sequence?)]
  #;[in-parallel ; FIXME listof
     (() #:rest (listof sequence?) . ->* . sequence?)]
  (def in-values-sequence
    (sequence? . -> . sequence?))
  (def in-values*-sequence
    (sequence? . -> . sequence?))
  ; [HO] stop-before stop-after
  (def make-do-sequence ; FIXME
    (any/c . -> . sequence?))
  (def-opq prop:sequence struct-type-property?)

  ;; 4.14.1.2 Sequence Conversion
  (def sequence->stream
    (sequence? . -> . stream?))
  (def sequence-generate
    (sequence? . -> . (values (-> boolean?) (-> any))))
  (def sequence-generate*
    (sequence? . -> . (values (or/c list? not)
                              (-> (values (or/c list? not) procedure?)))))

  ;; 4.14.1.3 Additional Sequence Operations
  (def-opq empty-sequence sequence?)
  (def sequence->list
    (sequence? . -> . list?))
  (def sequence-lengthx
    (sequence? . -> . exact-nonnegative-integer?))
  (def sequence-ref
    (sequence? exact-nonnegative-integer? . -> . any))
  (def sequence-tail
    (sequence? exact-nonnegative-integer? . -> . sequence?))
  #;[sequence-append ; FIXME listof
     (() #:rest (listof sequence?) . ->* . sequence?)]
  (def sequence-map
    ((any/c . -> . any/c) sequence? . -> . sequence?))
  ; [HO] sequence-andmap sequence-ormap
  (def sequence-for-each ; FIXME generalize 1st arg to multi args
    ((any/c . -> . any) sequence? . -> . void?))
  (def sequence-fold ; FIXME generalize 1st arg
    ((any/c any/c . -> . any/c) any/c sequence? . -> . any/c))
  (def sequence-count ; FIXME precise arity for 1st arg
    (procedure? sequence? . -> . exact-nonnegative-integer?))
  (def sequence-filter ; FIXME generalize 1st arg to multi args
    ((any/c . -> . boolean?) sequence? . -> . sequence?))
  (def sequence-add-between
    (sequence? any/c . -> . sequence?))
  #;[sequence/c ; FIXME uses, `contract?`
     (any/c . -> . any/c)]

  ; 4.14.1.3.1 Additional Sequence Constructors
  #;[in-syntax
     (syntax? . -> . sequence?)]
  (def in-slice
    (exact-positive-integer? sequence? . -> . sequence?))

     ;;;;; 4.14.2 Streams
  (def-pred stream?)
  (def-pred stream-empty? (stream?))
  (def stream-first
    ((and/c stream? (not/c stream-empty?)) . -> . any))
  (def stream-rest
    ((and/c stream? (not/c stream-empty?)) . -> . stream?))
  (def in-stream
    (stream? . -> . sequence?))
  (def-opq empty-stream stream?)
  (def stream->list
    (stream? . -> . list?))
  (def stream-length
    (stream? . -> . exact-nonnegative-integer?))
  (def stream-ref
    (stream? exact-nonnegative-integer? . -> . any))
  (def stream-tail
    (stream? exact-nonnegative-integer? . -> . stream?))
  #;[stream-append ; FIXME listof
     (() #:rest (listof stream?) . ->* . stream?)]
  (def stream-map
    (procedure? stream? . -> . stream?))
  ; [HO] stream-andmap stream-ormap
  (def stream-for-each ; FIXME varargs on 1st
    ((any/c . -> . any) stream? . -> . void?))
  (def stream-fold ; FIXME varargs on 1st
    ((any/c any/c . -> . any) any/c stream? . -> . any/c))
  (def stream-count ; FIXME varargs on 1st
    (procedure? stream? . -> . exact-nonnegative-integer?))
  (def stream-filter ; FIXME varargs on 1st
    ((any/c . -> . boolean?) stream? . -> . stream?))
  (def stream-add-between
    (stream? any/c . -> . stream?))
  (def-opq prop:stream struct-type-property?)
  (def stream/c
    (contract? . -> . contract?))

     ;;;;; 4.14.3 Generators
  (def-pred generator?)
  #;[yield ; FIXME uses
     (-> any)]
  (def generator-state
    (generator? . -> . symbol?))
  (def sequence->generator
    (sequence? . -> . (-> any)))
  (def sequence->repeated-generator
    (sequence? . -> . (-> any)))
  
  )
