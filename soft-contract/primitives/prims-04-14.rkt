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
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-14@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.14 Sequences and Streams
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-14@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^)
  (export)

  ;;;;; 4.14.1 Sequences

  ;; 4.14.1.1 Predicate and Constructors
  (def-pred sequence?)
  (def-prim/todo in-range ; FIXME uses
    (real? real? real? . -> . stream?))
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
  (def-prim in-hash
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
  
  )
