#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         "def-prim.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.1 Data-structure Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-prim/todo flat-named-contract ; FIXME uses
 (any/c flat-contract? . -> . flat-contract?))
(def-prim/todo any/c (any/c . -> . (not/c not)))
(def-prim/todo none/c (any/c . -> . not))
(def-prim/todo  or/c (contract? contract? . -> . contract?)) ; FIXME uses
(def-prim/todo and/c (contract? contract? . -> . contract?)) ; FIXME uses
(def-prim/todo not/c (flat-contract? . -> . flat-contract?))
(def-prim/todo =/c  (real? . -> . flat-contract?))
(def-prim/todo </c  (real? . -> . flat-contract?))
(def-prim/todo >/c  (real? . -> . flat-contract?))
(def-prim/todo <=/c (real? . -> . flat-contract?))
(def-prim/todo >=/c (real? . -> . flat-contract?))
(def-prim/todo between/c (real? real? . -> . flat-contract?))
[def-alias real-in between/c]
(def-prim/todo integer-in (exact-integer? exact-integer? . -> . flat-contract?))
(def-prim/todo char-in (char? char? . -> . flat-contract?))
(def-prim/todo def-alias natural-number/c exact-nonnegative-integer?)
(def-prim/todo string-len/c (real? . -> . flat-contract?))
(def-alias false/c not)
(def-pred printable/c)
#;[one-of/c
   (() #:rest (listof flat-contract?) . ->* . contract?)]
#;[symbols
   (() #:rest (listof symbol?) . ->* . flat-contract?)]
(def-prim/todo vectorof ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo vector-immutableof (contract? . -> . contract?))
(def-prim/todo vector/c ; FIXME uses
 (() #:rest (listof contract?) . ->* . contract?))
#;[vector-immutable/c
   (() #:rest (listof contract?) . ->* . contract?)]
(def-prim/todo box/c ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo box-immutable/c (contract? . -> . contract?))
(def-prim/todo listof (contract? . -> . list-contract?))
(def-prim/todo non-empty-listof (contract? . -> . list-contract?))
(def-prim/todo list*of (contract? . -> . contract?))
(def-prim/todo cons/c (contract? contract? . -> . contract?))
#;[list/c
   (() #:rest (listof contract?) . ->* . list-contract?)]
(def-prim/todo syntax/c (flat-contract? . -> . flat-contract?))
(def-prim/todo parameter/c ; FIXME uses
 (contract? . -> . contract?))
(def-prim/todo procedure-arity-includes/c
 (exact-nonnegative-integer? . -> . flat-contract?))
(def-prim/todo hash/c ; FIXME uses
 (chaperone-contract? contract? . -> . contract?))
(def-prim/todo channel/c (contract? . -> . contract?))
(def-prim/todo continuation-mark-key/c (contract? . -> . contract?))
;;[evt/c (() #:rest (listof chaperone-contract?) . ->* . chaperone-contract?)]
(def-prim/todo promise/c (contract? . -> . contract?))
(def-prim/todo flat-contract ((any/c . -> . any/c) . -> . flat-contract?))
(def-prim/todo flat-contract-predicate (flat-contract? . -> . (any/c . -> . any/c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.2 Function Contracts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-opq predicate/c contract?)
(def-opq the-unsupplied-arg unsupplied-arg?)
(def-pred unsupplied-arg?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TODO
(def-prim contract-first-order-passes?
 (contract? any/c . -> . boolean?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 8.8 Contract Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-pred contract?)
(def-pred chaperone-contract?)
(def-pred impersonator-contract?)
(def-pred flat-contract?)
(def-pred list-contract?)
(def-prim/todo contract-name (contract? . -> . any/c))
(def-prim/todo value-contract (has-contract? . -> . (or/c contract? not)))
[def-pred has-contract?]
(def-prim/todo value-blame (has-blame? . -> . (or/c blame? not)))
[def-pred has-blame?]
(def-prim/todo contract-projection (contract? . -> . (blame? . -> . (any/c . -> . any/c))))
(def-prim/todo make-none/c (any/c . -> . contract?))
(def-opq contract-continuation-mark-key continuation-mark-key?)
