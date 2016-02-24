#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/main.rkt" "../ast/main.rkt"
 "path-condition.rkt" "addr.rkt" "env.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (HashTable -α (℘ -V)))
(define-type -Δσ -σ)
(define ⊥σ : -σ (hash))
(define σ@ : (-σ -α → (℘ -V)) m@)

;; Look up store for exactly 1 value
(define (σ@¹ [σ : -σ] [α : -α])
  (define Vs (hash-ref σ α))
  (match (set-count Vs)
    [1 (set-first Vs)]
    [n
     (error 'σ@¹ "expect store to have exactly 1 value at address ~a, found ~a: ~a~n"
            (show-α α) n (set-map Vs show-V))]))

(: σ@/list : -σ (Listof -α) → (℘ (Listof -V)))
(define (σ@/list σ αs)
  (match αs
    [(cons α αs*)
     (define Vs (σ@ σ α))
     (define Vss (σ@/list σ αs*))
     (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
       (cons V Vs))]
    ['() {set '()}]))

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α Vs) σ])
    `(,(show-α α) ↦ ,@(set-map Vs show-V))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -Ξ (HashTable -ℬ (℘ -ℛ)))
(define-type -ΔΞ -Ξ)
(define ⊥Ξ : -Ξ (hash))
(define Ξ@ : (-Ξ -ℬ → (℘ -ℛ)) m@)

(define (show-Ξ [Ξ : -Ξ]) : (Listof Sexp)
  (for/list ([(ℬ ℛs) Ξ])
    `(,(show-ℬ ℬ) ↦ ,@(set-map ℛs show-ℛ))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (HashTable -ℬ (℘ -A)))
(define-type -ΔM -M)
(define ⊥M : -M (hash))
(define M@ : (-M -ℬ → (℘ -A)) m@)

(define (show-M [M : -M]) : (Listof Sexp)
  (for/list ([(ℬ As) M])
    `(,(show-ℬ ℬ) ↦ ,@(set-map As show-A))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -G.key ([expr : -γ] [ctx : -ρ]) #:transparent)
(struct -G.val ([cnd : -Γ] [res : -s] [renaming : -𝒳]) #:transparent)

;; Map path-condition address to possible path-condition, result, and renaming
(define-type -G (HashTable -G.key (℘ -G.val)))
(define ⊥G : -G (hash))
(define G@ : (-G -G.key → (℘ -G.val)) hash-ref) ; looking up something not there is an error

(define (show-G [G : -G]) : (Listof Sexp)
  (for/list ([(k vs) G])
    (match-define (-G.key γ ρ) k)
    `(,(show-γ γ) ,(show-ρ ρ)
      ↦
      ,@(for/list : (Listof Sexp) ([v vs])
          (match-define (-G.val Γ s 𝒳) v)
          `(,(show-Γ Γ) ,(show-s s) ,(show-𝒳 𝒳))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . 'undefined
            -prim
            (-●)
            (-St -struct-info (Listof (U -α.fld -α.var-car -α.var-cdr)))
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
              [rng : -⟦e⟧]
              [rng-env : -ρ])
            (-x/C [c : -α.x/c]))

(-Res . ::= . (-W [Vs : (Listof -V)] [s : -s])
              (-blm [violator : Mon-Party] [origin : Mon-Party] [c : -V] [v : (Listof -V)]))
(-Res/V . ::= . (Listof -V) -blm)

(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -A ([cnd : -Γ] [res : -Res]) #:transparent)
(struct -A* ([cnd : -Γ] [res : -Res/V]) #:transparent)
(define -A/V? (match-λ? (-A _ (? -W?))))

;; Constants & 'Macros'
(define -Null -null)
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -●/V (-●))
(define -●/Vs : (List -V) (list -●/V))
(define -Void/Vs (list (-b (void))))
(define -Void/W (-W -Void/Vs (-b (void))))
(define -integer?/W (-W¹ 'integer? 'integer?))
(define -number?/W (-W¹ 'number? 'number?))
(define -vector?/W (-W¹ 'vector? 'vector?))
(define -procedure?/W (-W¹ 'procedure? 'procedure?))
(define -vector-ref/W (-W¹ 'vector-ref 'vector-ref))
(define -vector-set/W (-W¹ 'vector-set! 'vector-set!))
(define -arity-includes?/W (-W¹ 'arity-includes? 'arity-includes?))
(define -=/W (-W¹ '= '=))
(define -contract-first-order-passes?/W (-W¹ 'contract-first-order-passes? 'contract-first-order-passes?))
(define -Vector₀ (-Vector '()))
;(define (-=/C [n : Integer]) (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) ⊥ρ))
;(define (-not/C [v : -v]) (-Clo '(x) (-@ 'not (list (-@ v (list (-x 'x)) -Λ)) -Λ) ⊥ρ))

(: C-flat? : -V → Boolean)
;; Check whether contract is flat, assuming it's already a contract
(define (C-flat? V)
  (match V
    [(-And/C flat? _ _) flat?]
    [(-Or/C flat? _ _) flat?]
    [(? -Not/C?) #t]
    [(-St/C flat? _ _) flat?]
    [(or (? -Vectorof?) (? -Vector/C?)) #f]
    [(? -=>i?) #f]
    [(or (? -Clo?) (? -Ar?) (? -prim?)) #t]
    [(? -x/C?) #t]
    [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-●) '●]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧ ρ) `(Clo ,(show-formals xs) ,(show-⟦e⟧ ⟦e⟧) ,(show-ρ ρ))]
    [(-Ar guard (cons α s) l³) `(,(show-V guard) ◃ (,(show-α α) @ ,(show-s s)))]
    [(-St s αs) `(,(show-struct-info s) ,@(map show-α αs))]
    [(-St/checked s γs _ α)
     `(,(string->symbol (format "~a/wrapped" (show-struct-info s)))
       ,@(for/list : (Listof Symbol) ([γ γs]) (if γ (show-α γ) '✓))
       ▹ ,(show-α α))]
    [(-Vector αs) `(vector ,@(map show-α αs))]
    [(-Vector/checked γs _ α) `(vector/wrapped ,@(map show-α γs) ▹ ,(show-α α))]
    [(-Vector/same γ _ α) `(vector/same ,(show-α γ) ▹ ,(show-α α))]
    [(-And/C _ l r) `(and/c ,(show-α l) ,(show-α r))]
    [(-Or/C _ l r) `(or/c ,(show-α l) ,(show-α r))]
    [(-Not/C γ) `(not/c ,(show-α γ))]
    [(-Vectorof γ) `(vectorof ,(show-α γ))]
    [(-Vector/C γs) `(vector/c ,@(map show-α γs))]
    [(-=>i doms rst ⟦d⟧ ρ)
     (define-values (xs cs)
       (for/lists ([xs : (Listof Symbol)] [cs : (Listof -s)])
                  ([dom : (Pairof Symbol -α.dom) doms])
         (match-define (cons x (-α.dom c)) dom)
         (values x (and (-e? c) c))))
     (match rst
       [#f
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-s c)))
              (res ,xs ,(show-⟦e⟧ ⟦d⟧)))]
       [(cons x* (and γ* (-α.rst c*)))
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-s c)))
              #:rest (,x* ,(if (-e? c*) (show-e c*) (show-α γ*)))
              (res ,xs ,(show-⟦e⟧ ⟦d⟧)))])]
    [(-St/C _ s αs)
     `(,(string->symbol (format "~a/c" (show-struct-info s))) ,@(map show-α αs))]
    [(-x/C (-α.x/c x)) `(recursive-contract ,(show-x/c x))]))

(define (show-A [A : -A])
  (match-define (-A Γ Res) A)
  `(A: ,(show-Γ Γ) ,(show-Res Res)))

(define (show-Res [Res : -Res]) : Sexp
  (cond [(-W? Res) (show-W Res)]
        [else (show-blm Res)]))

(define (show-W [W : -W]) : Sexp
  (match-define (-W Vs s) W)
  `(,@(map show-V Vs) @ ,(show-s s)))

(define (show-W¹ [W : -W¹]) : Sexp
  (match-define (-W¹ V s) W)
  `(,(show-V V) @ ,(show-s s)))

(define (show-blm [blm : -blm]) : Sexp
  (match-define (-blm l+ lo C Vs) blm)
  `(blame ,l+ ,lo ,(show-V C) ,(map show-V Vs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Evaluation context
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-ℰ . ::= . ;; Different type of context. Hack for now. I may de-hack some day but not a big problem. 
            (-ℰₚ.modules [cur-mod : -ℰ] [mods : (Listof -⟦e⟧)] [top : -⟦e⟧])
            ;; Different type of context. Hack for now. I may de-hack some day but not a big problem.
            (-ℰ.def [mod-name : Adhoc-Module-Path] [lhs : (Listof Symbol)] [rhs : -ℰ])
            (-ℰ.dec [name : -id] [ctc : -ℰ])
            
            ;; Regular context
            '□
            (-ℰ.if -ℰ -⟦e⟧ -⟦e⟧)
            (-ℰ.@ (Listof -W¹) -ℰ (Listof -⟦e⟧) -src-loc)
            (-ℰ.begin -ℰ (Listof -⟦e⟧))
            (-ℰ.begin0.v -ℰ (Listof -⟦e⟧))
            (-ℰ.begin0.e -W -ℰ (Listof -⟦e⟧))
            (-ℰ.let-values (Listof (Pairof Symbol -W¹))
                           (Listof Symbol)
                           -ℰ
                           (Listof (Pairof (Listof Symbol) -⟦e⟧))
                           -⟦e⟧
                           Mon-Party)
            (-ℰ.set! Symbol -ℰ)
            (-ℰ.μ/c Integer -ℰ)
            (-ℰ.struct/c -struct-info (Listof -W¹) -ℰ (Listof -⟦e⟧) Integer))

;; A "hole" ℋ is an evaluation context augmented with
;; path condition and information for converting answer's symbols
(struct -ℋ ([pc : -Γ] [aliases : -𝒳]
            [f : -s] [param->arg : (Listof (Pairof Symbol -s))]
            [ctx : -ℰ]) #:transparent)

(: show-ℰ ([-ℰ] [Sexp] . ->* . Sexp))
(define (show-ℰ ℰ [in-hole '□])
  (let loop ([ℰ : -ℰ ℰ])
    (match ℰ
      [(-ℰₚ.modules ℰ* ⟦m⟧s ⟦e⟧)
       `(,(loop ℰ*)
         ,(format "…~a modules…" (length ⟦m⟧s))
         ,"…top-level…")]
      [(-ℰ.def _ xs ℰ*)
       (define rhs (loop ℰ*))
       (match xs
         [(list x) `(define        ,x  ,rhs)]
         [_        `(define-values ,xs ,rhs)])]
      [(-ℰ.dec id ℰ*)
       `(provide/contract [,(-id-name id) ,(loop ℰ*)])]
      
      ['□ in-hole]
      [(-ℰ.if ℰ* _ _) `(if ,(loop ℰ*) … …)]
      [(-ℰ.@ Ws ℰ* ⟦e⟧s _) `(,@(map show-W¹ Ws) ,(loop ℰ*) ,(map (λ _ '…) ⟦e⟧s))]
      [(-ℰ.begin ℰ* ⟦e⟧s)
       `(begin ,(loop ℰ*) ,(format "…(~a)…" (length ⟦e⟧s)))])))

(define (show-ℋ [ℋ : -ℋ])
  (match-define (-ℋ Γ 𝒳 f bnds ℰ) ℋ)
  `(ℋ ,(show-Γ Γ) ,(show-𝒳 𝒳) ,(cons (show-s f) (show-bnds bnds)) ,(show-ℰ ℰ)))

(: show-bnds : (Listof (Pairof Symbol -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Symbol -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⟦e⟧ (-G -σ -ρ -Γ -𝒳 → (Values -Δσ (℘ -A) (℘ -ℐ))))
(define-values (show-⟦e⟧ show-⟦e⟧⁻¹) ((inst unique-name -⟦e⟧) '⟦e⟧))


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

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ ⟦e⟧ ρ) ℬ)
  `(ℬ ,(show-⟦e⟧ ⟦e⟧) ,(hash-keys ρ)))

(define (show-Co [Co : -Co]) : Sexp
  (match-define (-Co ℛ ans) Co)
  `(Co ,(show-ℛ ℛ) ,(set-map ans show-A)))

(define (show-ℐ [ℐ : -ℐ]) : Sexp
  (match-define (-ℐ ℋ ℬ) ℐ)
  `(ℐ ,(show-ℋ ℋ) ,(show-ℬ ℬ)))

(define (show-ℛ [ℛ : -ℛ]) : Sexp
  (match-define (-ℛ ℬ ℋ) ℛ)
  `(ℛ ,(show-ℬ ℬ) ,(show-ℋ ℋ)))


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
