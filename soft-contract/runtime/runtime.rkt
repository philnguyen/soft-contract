#lang typed/racket/base

(require
 racket/match racket/set
 "../utils/def.rkt" "../utils/set.rkt" "../utils/map.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt")

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Symbol -α))
(define ρ@ : (-ρ Symbol → -α) hash-ref)
(define ρ+ : (-ρ Symbol -α → -ρ) hash-set)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-s . ::= . -e #f)
(-Γ . ::= . (℘ -e))
(define ⊤Γ : -Γ ∅) ; the more it grows, the more precise
(define-type -𝒳 (HashTable Symbol -e))
(define ⊤𝒳 : -𝒳 (hash)) ; the more it grows, the more precise

(: Γ+ : -Γ -s → -Γ)
(define (Γ+ Γ s) (if s (set-add Γ s) Γ))

(: canonicalize : -𝒳 Symbol → -e)
;; Canonicalize a variable
(define (canonicalize 𝒳 x) (hash-ref 𝒳 x (λ () (-x x))))

(: canonicalize-e : -𝒳 -e → -e)
;; Canonicalize an expression
(define (canonicalize-e 𝒳 e)
  ((e/map (for/hash : (HashTable -e -e) ([(x e-x) 𝒳])
            (values (-x x) e-x)))
   e))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (HashTable -α (℘ -V)))
(define-type -Δσ -σ)
(define σ@ : (-σ -α → (℘ -V)) hash-ref)
(define ⊥σ : -σ (hash))

(define-type -M (HashTable -ℬ (℘ -A)))
(define-type -ΔM -M)
(define M@ : (-M -ℬ → (℘ -A)) hash-ref)
(define ⊥M : -M (hash))

(define-type -Ξ (HashTable -ℬ (℘ -ℛ)))
(define-type -ΔΞ -Ξ)
(define Ξ@ : (-Ξ -ℬ → (℘ -ℛ)) hash-ref)
(define ⊥Ξ : -Ξ (hash))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . 'undefined
            -prim
            (-●)
            (-St (Listof (U -α.fld -α.var-car -α.var-cdr)))
            (-St/checked
              [info : -struct-info] [contracts : (Listof (Option -α.struct/c))] [mon : Mon-Info]
              [unchecked : -α.st*])
            ;; Vectors
            (-Vector (Listof -α.idx))
            (-Vector/checked [contracts : (Listof -α.vector/c)] [mon : Mon-Info] [unchecked : -α.vct])
            (-Vector/same [contract : -α.vectorof] [mon : Mon-Info] [unchecked : -α.vct])
            ;; Functions
            (-Clo -formals -⟦e⟧ -ρ)
            (-Ar [#|ok, no recursion|# guard : -=>i] [v : (Pairof -α -s)] [l³ : Mon-Info])
            ;; Contracts
            ; Treat `and/c`, `or/c` specially to deal with `chaperone?`
            ; But these give rise to more special cases of stack frames
            (-And/C [flat? : Boolean] [l : -α.and/c-l] [r : -α.and/c-r])
            (-Or/C [flat? : Boolean] [l : -α.or/c-l] [r : -α.or/c-r])
            (-Not/C -α.not/c)
            (-Vectorof -α.vectorof)
            (-Vector/C (Listof -α.vector/c))
            (-St/C [flat? : Boolean] [info : -struct-info] [fields : (Listof -α.struct/c)])
            (-=>i
              [doms : (Listof (Pairof Symbol -α.dom))]
              [rst : (Option (Pairof Symbol -α.rst))]
              [rng : -ℬ])
            (-x/C [c : -α.x/c]))

(struct -blm ([violator : Mon-Party] [origin : Mon-Party] [c : -V] [v : (Listof -V)]) #:transparent)

(struct -W ([Vs : (Listof -V)] [s : -s]) #:transparent)
(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(-Res . ::= . -W -blm)
(struct -A ([cnd : -Γ] [res : -Res]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compiled expression
(define-type -⟦e⟧ (-M -σ -ρ -Γ -𝒳 → (Values -Δσ (℘ -A) (℘ -ℐ))))
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
            (-ℰ.if -ℰ -⟦e⟧ -⟦e⟧)
            (-ℰ.@ (Listof -W¹) -ℰ (Listof -⟦e⟧) -src-loc)
            #;(-ℰ.begin -ℰ (Listof -⟦e⟧))
            #;(-ℰ.begin0.v -ℰ (Listof -⟦e⟧))
            #;(-ℰ.begin0.e -W -ℰ (Listof -⟦e⟧)))

;; A "hole" ℋ is an evaluation context augmented with
;; path condition and information for converting answer's symbols
(struct -ℋ ([pc : -Γ] [aliases : -𝒳] [f : -s] [param->arg : -𝒳] [ℰ : -ℰ]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Collecting operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (for*/ans (clause ...) e ...)
  (for*/fold ([δσ : -Δσ ⊥σ] [As : (℘ -A) ∅] [ℐs : (℘ -ℐ) ∅])
             (clause ...)
    (define-values (δσ* As* ℐs*) (let () e ...))
    (values (⊔/m δσ δσ*) (∪ As As*) (∪ ℐs ℐs*))))

(define-syntax ⊔/ans
  (syntax-rules ()
    [(_) (⊥ans)]
    [(_ ans) ans]
    [(_ ans₁ ans ...)
     (let-values ([(δσ₁ As₁ ℐs₁) ans₁]
                  [(δσ₂ As₂ ℐs₂) (⊔/ans ans ...)])
       (values (⊔/m δσ₁ δσ₂) (∪ As₁ As₂) (∪ ℐs₁ ℐs₂)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Shorhands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (⊥ans) (values ⊥σ ∅ ∅))
(define-syntax-rule (with-Γ Γ e) (if Γ e (⊥ans)))
