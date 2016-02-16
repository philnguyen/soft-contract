#lang typed/racket/base

(provide (all-defined-out)
         (all-from-out "path-condition.rkt" "addr.rkt" "env.rkt"))

(require
 racket/match racket/set
 "../utils/main.rkt" "../ast/main.rkt"
 "path-condition.rkt" "addr.rkt" "env.rkt")


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

(-Res . ::= . (-W [Vs : (Listof -V)] [s : -s])
              (-blm [violator : Mon-Party] [origin : Mon-Party] [c : -V] [v : (Listof -V)]))

(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -A ([cnd : -Γ] [res : -Res]) #:transparent)


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
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⟦e⟧ (-M -σ -ρ -Γ -𝒳 → (Values -Δσ (℘ -A) (℘ -ℐ))))
(define-type -⟦ℰ⟧ (-⟦e⟧ → -⟦e⟧))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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
