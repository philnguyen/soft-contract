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
  (struct -α.x [ctx : (U Integer (Pairof Symbol -Γ))])
  ;Symbol

  ;; for mutable or opaque field
  (struct -α.fld [ctx : (U Integer -e (List -id Integer Integer))])
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
  (struct -α.vector/c [ctx : (U Integer (Pairof Integer Integer) -e)])
  (struct -α.vectorof [ctx : (U Integer -e)])
  (struct -α.struct/c [ctx : (U Integer (List -id Integer Integer) -e)])
  (struct -α.x/c [pos : Integer])
  (struct -α.dom [ctx : (U Integer (Pairof Integer Integer) -e)])
  (struct -α.rst [ctx : (U Integer -e)])
  )

(: alloc-fields : -struct-info (Listof -?e) Integer → (Listof -α.fld))
(define (alloc-fields s args pos)
  (match-define (-struct-info id n _) s)
  (for/list ([i n] [?e args])
    (-α.fld (or ?e (list id pos i)))))

(define-values (show-α show-α⁻¹) ((inst unique-name -α) 'α))


;;;;; Hack for refactoring verification and counterexamples
(define-parameter mk-α.x : ((U Integer (Pairof Symbol -Γ)) → -α.x) -α.x)
(define-parameter mk-α.fld : ((U -e (List -id Integer Integer)) → -α.fld) -α.fld)
(define-parameter mk-α.var-car : (Integer Natural → -α.var-car) -α.var-car)
(define-parameter mk-α.var-cdr : (Integer Natural → -α.var-cdr) -α.var-cdr)
(define-parameter mk-α.st* : (-id Integer → -α.st*) -α.st*)
(define-parameter mk-α.idx : (Integer Integer → -α.idx) -α.idx)
(define-parameter mk-α.vct : (Integer → -α.vct) -α.vct)
(define-parameter mk-α.and/c-l : ((U Integer -e) → -α.and/c-l) -α.and/c-l)
(define-parameter mk-α.and/c-r : ((U Integer -e) → -α.and/c-r) -α.and/c-r)
(define-parameter mk-α.or/c-l : ((U Integer -e) → -α.or/c-l) -α.or/c-l)
(define-parameter mk-α.or/c-r : ((U Integer -e) → -α.or/c-r) -α.or/c-r)
(define-parameter mk-α.not/c : ((U Integer -e) → -α.not/c) -α.not/c)
(define-parameter mk-α.vector/c : ((U Integer (Pairof Integer Integer) -e) → -α.vector/c) -α.vector/c)
(define-parameter mk-α.vectorof : ((U Integer -e) → -α.vectorof) -α.vectorof)
(define-parameter mk-α.struct/c : ((U Integer (List -id Integer Integer) -e) → -α.struct/c) -α.struct/c)
(define-parameter mk-α.dom : ((U Integer (Pairof Integer Integer) -e) → -α.dom) -α.dom)
(define-parameter mk-α.rst : ((U Integer -e) → -α.rst) -α.rst)

(define fresh-addr! (make-nat-src))
(define-syntax-rule (make-fresh-func f) (λ (x) (if (-e? x) (f x) (f (fresh-addr!)))))
(define-syntax-rule (make-fresh-func₂ f) (λ (x _) (f x (fresh-addr!))))

(define-syntax-rule (with-concrete-allocation e ...)
  (parameterize ([mk-α.x (make-fresh-func -α.x)]
                 [mk-α.fld (make-fresh-func -α.fld)]
                 [mk-α.var-car (make-fresh-func₂ -α.var-car)]
                 [mk-α.var-cdr (make-fresh-func₂ -α.var-cdr)]
                 [mk-α.st* (make-fresh-func₂ -α.st*)]
                 [mk-α.idx (make-fresh-func₂ -α.idx)]
                 [mk-α.vct (make-fresh-func -α.vct)]
                 [mk-α.and/c-l (make-fresh-func -α.and/c-l)]
                 [mk-α.and/c-r (make-fresh-func -α.and/c-r)]
                 [mk-α.or/c-l (make-fresh-func -α.or/c-l)]
                 [mk-α.or/c-r (make-fresh-func -α.or/c-r)]
                 [mk-α.not/c (make-fresh-func -α.not/c)]
                 [mk-α.vector/c (make-fresh-func -α.vector/c)]
                 [mk-α.vectorof (make-fresh-func -α.vectorof)]
                 [mk-α.struct/c (make-fresh-func -α.struct/c)]
                 [mk-α.dom (make-fresh-func -α.dom)]
                 [mk-α.rst (make-fresh-func -α.rst)]
                 )
    e ...))
