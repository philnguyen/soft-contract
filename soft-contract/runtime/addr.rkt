#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match
 "../utils/def.rkt" "../utils/pretty.rkt"
 "../ast/definition.rkt" "path-inv.rkt")

;; Just to make it easy to catch mis-allocation
(define-data -α
  ;; for top-level definition and contract
  (struct -α.def [id : -id])
  (struct -α.ctc [id : -id])

  ;; for lexical binding
  (struct -α.x [x : Symbol] #;[arg : -?e] [inv : -Γ])
  ;Symbol

  ;; TODO: temp hack
  (struct -α.tmp [v : -e])

  ;; for mutable or opaque field
  (struct -α.fld [ctx : (U -e (List -id Integer Integer))])
  ; for Cons/varargs
  (struct -α.var-car [pos : Integer] [idx : Natural]) ; idx helps prevent infinite list
  (struct -α.var-cdr [pos : Integer] [idx : Natural])

  ;; for wrapped mutable struct
  (struct -α.st* [id : -id] [pos : Integer])

  ;; for vector indices
  (struct -α.idx [pos : Integer] [idx : Integer])

  ;; for inner vector
  (struct -α.vct [pos : Integer])

  ;; for contract components
  (struct -α.and/c-l [ctx : (U Integer -e)])
  (struct -α.and/c-r [ctx : (U Integer -e)])
  (struct -α.or/c-l [ctx : (U Integer -e)])
  (struct -α.or/c-r [ctx : (U Integer -e)])
  (struct -α.not/c [ctx : (U Integer -e)])
  (struct -α.vector/c [ctx : (U (Pairof Integer Integer) -e)])
  (struct -α.vectorof [ctx : (U Integer -e)])
  (struct -α.struct/c [ctx : (U (List -id Integer Integer) -e)])
  (struct -α.x/c [pos : Integer])
  (struct -α.dom [ctx : (U (Pairof Integer Integer) -e)])
  (struct -α.rst [ctx : (U Integer -e)])
  )

(: alloc-fields : -struct-info (Listof -?e) Integer → (Listof -α.fld))
(define (alloc-fields s args pos)
  (match-define (-struct-info id n _) s)
  (for/list ([i n] [?e args])
    (-α.fld (or ?e (list id pos i)))))

(define-values (show-α show-α⁻¹) ((inst unique-name -α) 'α))
