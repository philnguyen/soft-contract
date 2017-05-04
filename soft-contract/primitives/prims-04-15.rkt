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
         "../runtime/main.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-15@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.15 Dictionaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-15@
  (import prim-runtime^ proof-system^ widening^)
  (export)

  ;;;;; 4.15.1 Dictionary Predicates and Contracts
  (def-pred/todo dict?)
  (def-prim/todo dict-implements? ; FIXME varargs
    (dict? symbol? . -> . boolean?))
  #;[dict-implements/c ; FIXME varargs, contracts
     (symbol? . -> . flat-contract?)]
  [def-pred dict-mutable? (dict?)]
  [def-pred dict-can-remove-keys? (dict?)]
  [def-pred dict-can-functional-set? (dict?)]

     ;;;;; 4.15.2 Generic Dictionary Interface
  (def-opq prop:dict struct-type-property?)

  ;; 4.15.2.1 Primitive Dictionary Methods
  (def-prim/todo dict-ref ; FIXME use
    (dict? any/c . -> . any))
  (def-prim/todo dict-set!
    ((and/c dict? (not/c immutable?)) any/c any/c . -> . void?))
  (def-prim/todo dict-set
    ((and/c dict? immutable?) any/c any/c . -> . (and/c dict? immutable?)))
  (def-prim/todo dict-remove!
    ((and/c dict? (not/c immutable?)) any/c . -> . void?))
  (def-prim/todo dict-remove
    ((and/c dict? immutable?) any/c . -> . (and/c dict? immutable?)))
  (def-prim/todo dict-iterate-first
    (dict? . -> . any/c))
  (def-prim/todo dict-iterate-next
    (dict? any/c . -> . any/c))
  (def-prim/todo dict-iterate-key
    (dict? any/c . -> . any))
  (def-prim/todo dict-iterate-value
    (dict? any/c . -> . any))

  ;; 4.15.2.2 Derived Dictionary Methods
  [def-pred dict-has-key? (dict? any/c)]
  (def-prim/todo dict-set*! ; FIXME use
    ((and/c dict? (not/c immutable?)) any/c any/c . -> . void?))
  (def-prim/todo dict-set* ; FIXME use
    ((and/c dict? immutable?) any/c any/c . -> . (and/c dict? immutable?)))
  (def-prim/todo dict-ref!
    (dict? any/c any/c . -> . any))
  (def-prim/todo dict-update! ; FIXME use
    ((and/c dict? (not/c immutable?)) any/c (any/c . -> . any/c) . -> . void?))
  (def-prim/todo dict-update
    ((and/c dict? immutable?) any/c (any/c . -> . any/c) . -> . (and/c dict? immutable?)))
  #;[dict-map ; FIXME listof
     (dict? (any/c any/c . -> . any/c) . -> . (listof any/c))]
  (def-prim/todo dict-for-each
    (dict? (any/c any/c . -> . any) . -> . void?))
  (def-pred dict-empty? (dict?))
  (def-prim/todo dict-count
    (dict? . -> . exact-nonnegative-integer?))
  (def-prim/todo dict-copy
    (dict? . -> . dict?))
  (def-prim/todo dict-clear
    (dict? . -> . dict?))
  (def-prim/todo dict-clear!
    (dict? . -> . void?))
  [def-prims (dict-keys dict-values)
    (dict? . -> . list?)]
  #;[dict->list ; TODO more precise than doc. Confirm. ; FIXME listof
     (dict? . -> . (listof pair?))]

;;;;; 4.15.3 Dictionary Sequences
  (def-prim/todo in-dict
    (dict? . -> . sequence?))
  (def-prims (in-dict-keys in-dict-values)
    (dict? . -> . sequence?))
  (def-prim/todo in-dict-pairs
    (dict? . -> . sequence?))

;;;;; 4.15.4 Contracted Dictionaries
  (def-opq prop:dict/contract struct-type-property?)
  #;[def-prims (dict-key-contract dict-value-contract dict-iter-contract) ; FIXME contract?
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
  [def-prims (#:todo make-custom-hash make-weak-custom-hash make-immutable-custom-hash) ; FIXME uses
    ((or/c (any/c any/c . -> . any/c)
           (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
     . -> . dict?)]

  )
