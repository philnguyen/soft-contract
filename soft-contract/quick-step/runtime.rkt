#lang typed/racket/base

(require
 racket/match racket/set
 "../utils/def.rkt" "../utils/set.rkt" "../utils/map.rkt"
 "../ast/definition.rkt")

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Symbol (Pairof -α -s)))

(: canonicalize : -ρ -s → -s)
;; Resolve aliasing
(define (canonicalize ρ s) #|TODO|# s)

(: ρ@ : -ρ Symbol → -α)
(define (ρ@ ρ x) (car (hash-ref ρ x)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-s . ::= . -e #f)
(-Γ . ::= . (℘ -e))
(define ⊤Γ : -Γ ∅)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (HashTable -α (℘ -V)))
(define-type -M (HashTable -ℬ (℘ -A)))
(define-type -Ξ (HashTable -ℬ (℘ -ℛ)))
(define-type -Δσ -σ)
(define-type -ΔM -M)
(define-type -ΔΞ -Ξ)
(define ⊥σ : -σ (hash))
(define ⊥M : -M (hash))
(define ⊥Ξ : -Ξ (hash))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . 'undefined
    -prim
    (struct -●)
    (struct -St [-struct-info (Listof (U -α.fld -α.var-car -α.var-cdr))])
    (struct -St/checked
      [info : -struct-info] [contracts : (Listof (Option -α.struct/c))] [mon : Mon-Info]
      [unchecked : -α.st*])
    ;; Vectors
    (struct -Vector [fields : (Listof -α.idx)])
    (struct -Vector/checked [contracts : (Listof -α.vector/c)] [mon : Mon-Info] [unchecked : -α.vct])
    (struct -Vector/same [contract : -α.vectorof] [mon : Mon-Info] [unchecked : -α.vct])
    ;; Functions
    (struct -Clo [xs : -formals] [e : -⟦e⟧] [ρ : -ρ])
    (struct -Ar [#|ok, no recursion|# guard : -=>i] [v : (Pairof -α -s)] [l³ : Mon-Info])
    ;; Contracts
    ; Treat `and/c`, `or/c` specially to deal with `chaperone?`
    ; But these give rise to more special cases of stack frames
    (struct -And/C [flat? : Boolean] [l : -α.and/c-l] [r : -α.and/c-r])
    (struct -Or/C [flat? : Boolean] [l : -α.or/c-l] [r : -α.or/c-r])
    (struct -Not/C [γ : -α.not/c])
    (struct -Vectorof [γ : -α.vectorof])
    (struct -Vector/C [γs : (Listof -α.vector/c)])
    (struct -St/C [flat? : Boolean] [info : -struct-info] [fields : (Listof -α.struct/c)])
    (struct -=>i
      [doms : (Listof (Pairof Symbol -α.dom))]
      [rst : (Option (Pairof Symbol -α.rst))]
      [rng : -ℬ])
    (struct -x/C [c : -α.x/c]))

(struct -blm ([violator : Mon-Party] [origin : Mon-Party] [c : -V] [v : -Vs]) #:transparent)

(struct (X) -W ([x : X] [e : -s]) #:transparent)
(-WV . ::= . (-W -V))
(-Vs . ::= . (Listof -V))
(-WVs . ::= . (-W -Vs))
(-Res . ::= . -WVs -blm)
(struct -A ([cnd : -Γ] [res : -Res]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compiled expression
(define-type -⟦e⟧ (-M -σ -ℬ → (Values -Δσ (℘ -A) (℘ -ℐ))))
(define-type -⟦ℰ⟧ (-⟦e⟧ → -⟦e⟧))

;; Evaluation "unit" / "stack address"
(struct -ℬ ([exp : -⟦e⟧] [env : -ρ]) #:transparent)

;; Continued evaluation
(struct -Co ([cont : -ℛ] [ans : (℘ -A)]) #:transparent)

;; Suspended, "intermediate" expression ℐ ≡ ℋ[ℬ]
(struct -ℐ ([hole : -ℋ] ; caller's hole
            [target : -ℬ] ; callee's context/address
            ) #:transparent)

;; Return point / continuation (deliberately distinct from `-ℋ`)
(struct -ℛ ([ctx : -ℬ] ; caller's context/address
            [hole : -ℋ] ; caller's continuation and path condition
            ) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Evaluation context
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-ℰ . ::= . '□
            (struct -ℰ.if [-ℰ -⟦e⟧ -⟦e⟧])
            (struct -ℰ.@ [(Listof -WV) -ℰ (Listof -⟦e⟧) -src-loc])
            #;(struct -ℰ.begin [-ℰ (Listof -⟦e⟧)])
            #;(struct -ℰ.begin0.v [-ℰ (Listof -⟦e⟧)])
            #;(struct -ℰ.begin0.e [-WV -ℰ (Listof -⟦e⟧)]))

;; A "hole" ℋ is an evaluation context augmented with
;; path condition and information for converting answer's symbols
(struct -ℋ ([pc : -Γ] [f : -s] [param->arg : (HashTable Symbol -s)] [ℰ : -ℰ]) #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-α . ::= . ; For top-level definition and contract
            (struct -α.def [-id])
            (struct -α.ctc [-id])
            ; for binding
            (struct -α.x [Symbol -⟦e⟧ -Γ])
            ; for mutable or opaque field
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
            (struct -α.rst [ctx : (U Integer -e)]))

(: alloc-fields : -struct-info (Listof -s) Integer → (Listof -α.fld))
(define (alloc-fields s args pos)
  (match-define (-struct-info id n _) s)
  (for/list ([i n] [?e args])
    (-α.fld (or ?e (list id pos i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Collecting operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (for*/ans (clause ...) e ...)
  (for*/fold ([δσ : -Δσ ⊥σ] [As : (℘ -A) ∅] [ℋs : (℘ -ℐ) ∅])
             (clause ...)
    (define-values (δσ* As* ℐs*) (begin e ...))
    (values (⊔/m δσ δσ*) (∪ As As*) (∪ ℐs ℐs*))))
