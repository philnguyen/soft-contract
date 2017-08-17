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

(provide prims-04-16@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.16 Sets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-16@
  (import prim-runtime^ proof-system^ widening^ val^ pc^ sto^)
  (export)

  ;;;;; Hash Sets
  (def-preds (set-equal? set-eqv? set-eq? set? set-mutable? set-weak?))
  (def-prim set
    (() #:rest list? . ->* . (and/c generic-set? set-equal? set?)))
  (def-prim/todo seteqv
    (() #:rest list? . ->* . (and/c generic-set? set-eqv? set?)))
  (def-prim/todo seteq
    (() #:rest list? . ->* . (and/c generic-set? set-eq? set?)))
  (def-prim/todo mutable-set
    (() #:rest list? . ->* . (and/c generic-set? set-equal? set-mutable?)))
  (def-prim/todo mutable-seteqv
    (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-mutable?)))
  (def-prim/todo mutable-seteq
    (() #:rest list? . ->* . (and/c generic-set? set-eq? set-mutable?)))
  (def-prim/todo weak-set
    (() #:rest list? . ->* . (and/c generic-set? set-equal? set-weak?)))
  (def-prim/todo weak-seteqv
    (() #:rest list? . ->* . (and/c generic-set? set-eqv? set-weak?)))
  (def-prim/todo weak-seteq
    (() #:rest list? . ->* . (and/c generic-set? set-eq? set-weak?)))
  (def-prim/todo list->set
    (list? . -> . (and/c generic-set? set-equal? set?)))
  (def-prim/todo list->seteqv
    (list? . -> . (and/c generic-set? set-eqv? set?)))
  (def-prim/todo list->seteq
    (list? . -> . (and/c generic-set? set-eq? set?)))
  (def-prim/todo list->mutable-set
    (list? . -> . (and/c generic-set? set-equal? set-mutable?)))
  (def-prim/todo list->mutable-seteqv
    (list? . -> . (and/c generic-set? set-eqv? set-mutable?)))
  (def-prim/todo list->mutable-seteq
    (list? . -> . (and/c generic-set? set-eq? set-mutable?)))
  (def-prim/todo list->weak-set
    (list? . -> . (and/c generic-set? set-equal? set-weak?)))
  (def-prim/todo list->weak-seteqv
    (list? . -> . (and/c generic-set? set-eqv? set-weak?)))
  (def-prim/todo list->weak-seteq
    (list? . -> . (and/c generic-set? set-eq? set-weak?)))

;;;;; 4.16.2 Set Predicates and Contracts
  (def-pred generic-set?)
  #;[set-implements ; FIXME listof
     ((generic-set?) #:rest (listof symbol?) . ->* . boolean?)]
  #;[set-implements/c ; FIXME varargs, contract?
     (symbol? . -> . flat-contract?)]
  #;[set/c ; FIXME uses, contract?
     (chaperone-contract? . -> . contract?)]

;;;;; 4.16.3 Generic Set Interface

  ;; 4.16.3.1 Set Methods
  [def-pred set-member? (generic-set? any/c)]
  [def-prims (set-add set-remove)
    ((and/c generic-set? (not/c set-mutable?)) any/c . -> . generic-set?)]
  [def-prims (set-add! set-remove!)
    ((and/c generic-set? set-mutable?) any/c . -> . void?)]
  [def-pred set-empty? (generic-set?)]
  (def-prim/todo set-count
    (generic-set? . -> . exact-nonnegative-integer?))
  (def-prim/todo set-first
    ((and/c generic-set? (not/c set-empty?)) . -> . any/c))
  (def-prim/todo set-rest ; TODO probably refine with (im)mutable? and other modifiers
    ((and/c generic-set? (not/c set-empty?)) . -> . generic-set?))
  (def-prim/todo set->stream
    (generic-set? . -> . stream?))
  (def-prim/todo set-copy
    (generic-set? . -> . generic-set?))
  (def-prim/todo set-copy-clear
    (generic-set? . -> . (and/c generic-set? set-empty?)))
  (def-prim/todo set-clear
    ((and/c generic-set? (not/c set-mutable?)) . -> . (and/c generic-set? set-empty?)))
  (def-prim/todo set-clear!
    ((and/c generic-set? set-mutable?) . -> . void?))
  ;; FIXME listof

  (def-prim set-union
    ; FIXME enforce sets of the same type
    ; FIXME uses
    #;((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?)
    (set? set? . -> . set?))
  #|
  (def-prim/todo set-union! ; FIXME enforce sets of the same type
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
  (def-prim/todo set-intersect
  ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
  (def-prim/todo set-intersect!
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
  (def-prim/todo set-subtract
  ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
  (def-prim/todo set-subtract!
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))
  (def-prim/todo set-symmetric-difference
  ((generic-set?) #:rest (listof generic-set?) . ->* . generic-set?))
  (def-prim/todo set-symmetric-difference!
  ((generic-set?) #:rest (listof generic-set?) . ->* . void?))|#
  (def-prims (set=? subset? proper-subset?) ; FIXME enforce same `set` type
    (generic-set? generic-set? . -> . boolean?))
  (def-prim/todo set->list
    (generic-set? . -> . list?))
  #;[set-map ; FIXME listof
     (generic-set? (any/c . -> . any/c) . -> . (listof any/c))]
  (def-prim/todo set-for-each
    (generic-set? (any/c . -> . any) . -> . void?))
  (def-prim/todo in-set
    (generic-set? . -> . sequence?))

;;;;; 4.16.4 Custom Hash Sets
  #;[make-custom-set-types ; FIXME uses
     ((or/c (any/c any/c . -> . any/c)
            (any/c any/c (any/c any/c . -> . any/c) . -> . any/c))
      . -> .
      (values (any/c . -> . boolean?)
              (any/c . -> . boolean?)
              (any/c . -> . boolean?)
              (any/c . -> . boolean?)
              ([] [stream?] . ->* . generic-set?)
              ([] [stream?] . ->* . generic-set?)
              ([] [stream?] . ->* . generic-set?)))]
  )
