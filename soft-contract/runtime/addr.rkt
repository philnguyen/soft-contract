#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match
 "../utils/def.rkt" "../utils/pretty.rkt"
 "../ast/definition.rkt")

;; Just to make it easy to catch mis-allocation
(define-data -α
  ;; for top-level definition and contract
  (struct -α.def [id : -id])
  (struct -α.ctc [id : -id])

  ;; for lexical binding
  ;(struct -α.bnd [x : Symbol] [arg : -?e] [inv : -Γ])
  Symbol

  ;; TODO: temp hack
  (struct -α.tmp [v : -e])

  ;; for mutable or opaque field
  (struct -α.fld [id : -id] [pos : Integer] [idx : Integer])
  ; for Cons/varargs
  (struct -α.var-car [pos : Integer] [idx : Integer])
  (struct -α.var-cdr [pos : Integer] [idx : Integer])

  ;; for wrapped mutable struct
  (struct -α.st* [id : -id] [pos : Integer])

  ;; for vector indices
  (struct -α.idx [pos : Integer] [idx : Integer])

  ;; for inner vector
  (struct -α.vct [pos : Integer])

  ;; for contract components
  (struct -α.and/c-l [pos : Integer])
  (struct -α.and/c-r [pos : Integer])
  (struct -α.or/c-l [pos : Integer])
  (struct -α.or/c-r [pos : Integer])
  (struct -α.not/c [pos : Integer])
  (struct -α.vector/c [pos : Integer] [idx : Integer])
  (struct -α.vectorof [pos : Integer])
  (struct -α.struct/c [id : -id] [pos : Integer] [idx : Integer])
  (struct -α.x/c [pos : Integer])
  )

(: alloc-fields : -struct-info Integer → (Listof -α.fld))
(define (alloc-fields s loc)
  (match-define (-struct-info id n _) s)
  (for/list ([i n]) (-α.fld id loc i)))

(define show-α : (-α → Symbol) (unique-name 'α))
