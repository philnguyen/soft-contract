#lang typed/racket/base

(require
 racket/match
 "../utils/main.rkt" "../ast/definition.rkt"
 "path-condition.rkt")

(provide (all-defined-out))

(-α . ::= . ; For top-level definition and contract
            (-α.def -id)
            (-α.ctc -id)
            ; for binding
            (-α.x Symbol -Γ) ; 1-CFA ish, TODO: fix
            ; for mutable or opaque field
            (-α.fld (U Integer -e (List -id Integer Integer)))
            ; for Cons/varargs
            (-α.var-car [pos : Integer] [idx : Natural]) ; idx helps prevent infinite list 
            (-α.var-cdr [pos : Integer] [idx : Natural])

            ;; for wrapped mutable struct
            (-α.st* [id : -id] [pos : Integer])

            ;; for vector indices
            (-α.idx [pos : Integer] [idx : Integer])

            ;; for inner vector
            (-α.vct [pos : Integer])

            ;; for contract components
            (-α.and/c-l (U Integer -e))
            (-α.and/c-r (U Integer -e))
            (-α.or/c-l (U Integer -e))
            (-α.or/c-r (U Integer -e))
            (-α.not/c (U Integer -e))
            (-α.vector/c (U Integer (Pairof Integer Integer) -e))
            (-α.vectorof (U Integer -e))
            (-α.struct/c (U Integer (List -id Integer Integer) -e))
            (-α.x/c [pos : Integer])
            (-α.dom (U Integer (Pairof Integer Integer) -e))
            (-α.rst (U Integer -e)))

(: alloc-fields : -struct-info (Listof -s) Integer → (Listof -α.fld))
(define (alloc-fields s args pos)
  (match-define (-struct-info id n _) s)
  (for/list ([i n] [?e args])
    (-α.fld (or ?e (list id pos i)))))

(define-values (show-α show-α⁻¹) ((inst unique-name -α) 'α))
