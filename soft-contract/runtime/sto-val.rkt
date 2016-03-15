#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set racket/list
 "../utils/main.rkt" "../ast/main.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Symbol -α))
(define-type -Δρ -ρ)
(define ⊥ρ : -ρ (hasheq))
(define ρ@ : (-ρ Symbol → -α) hash-ref)
(define ρ+ : (-ρ Symbol -α → -ρ) hash-set)

(: ρ++ : -ρ -Δρ → -ρ)
(define (ρ++ ρ δρ)
  (for/fold ([ρ : -ρ ρ]) ([(x α) δρ])
    (hash-set ρ x α)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (HashTable -α (℘ -V)))
(define-type -Δσ -σ)
(define ⊥σ : -σ (hash))

(: σ@ : -σ -α → (℘ -V))
(define (σ@ σ α)
  (hash-ref σ α (λ () (error 'σ@ "non-existent address ~a" α))))

(: σ@/list : -σ (Listof -α) → (℘ (Listof -V)))
;; Look up store at addresses. Return all possible combinations
(define (σ@/list σ αs)
  (match αs
    [(cons α αs*)
     (define Vs (σ@ σ α))
     (define Vss (σ@/list σ αs*))
     (for*/set: : (℘ (Listof -V)) ([V Vs] [Vs Vss])
       (cons V Vs))]
    ['() {set '()}]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -Ξ (HashTable -ℬ (℘ -ℛ)))
(define-type -ΔΞ -Ξ)
(define ⊥Ξ : -Ξ (hash))
(define Ξ@ : (-Ξ -ℬ → (℘ -ℛ)) m@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (HashTable -ℬ (℘ -A)))
(define-type -ΔM -M)
(define ⊥M : -M (hash))
(define M@ : (-M -ℬ → (℘ -A)) m@)


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
            (-Clo -formals -⟦e⟧ -ρ -Γ)
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
            (-=>i [doms : (Listof -α.dom)] [#|ok, no recursion|# rng : -Clo])
            (-x/C [c : -α.x/c]))

(struct -blm ([violator : Mon-Party] [origin : Mon-Party]
              [c : (Listof -V)] [v : (Listof -V)]) #:transparent)
(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -W ([Vs : (Listof -V)] [s : -s]) #:transparent)
(struct -ΓW ([cnd : -Γ] [W : -W]) #:transparent)
(struct -ΓE ([cnd : -Γ] [blm : -blm]) #:transparent)
(-A . ::= . -ΓW -ΓE)
(-A* . ::= . (Listof -V) -blm)


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
                           (Pairof (Listof Symbol) -ℰ)
                           (Listof (Pairof (Listof Symbol) -⟦e⟧))
                           -⟦e⟧
                           Mon-Party)
            (-ℰ.letrec-values -Δρ
                              (Pairof (Listof Symbol) -ℰ)
                              (Listof (Pairof (Listof Symbol) -⟦e⟧))
                              -⟦e⟧
                              Mon-Party)
            (-ℰ.set! Symbol -ℰ)
            (-ℰ.μ/c Integer -ℰ)
            (-ℰ.-->i (Listof -W¹) -ℰ (Listof -⟦e⟧) -W¹ Integer)
            (-ℰ.struct/c -struct-info (Listof -W¹) -ℰ (Listof -⟦e⟧) Integer))

;; A "hole" ℋ is an evaluation context augmented with
;; caller's path condition and information for renaming callee's symbols
(struct -ℋ ([pc : -Γ] [f : -s] [param->arg : (Listof (Pairof Symbol -s))]
            [ctx : -ℰ]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Symbolic value is either pure, refinable expression, or the conservative unrefinable `#f`
(-s . ::= . -e #f)

(: s↓ : -s (℘ Symbol) → -s)
;; Restrict symbol to given set of free variables
(define (s↓ s xs)
  (and s (e↓ s xs)))
(: e↓ : -e (℘ Symbol) → -s)
(define (e↓ e xs)
  (and (⊆ (fv e) xs) e))

;; Path condition is set of (pure) expression known to have evaluated to non-#f
(struct -Γ ([facts : (℘ -e)]
            [aliases : (HashTable Symbol -e)]
            [tails : (℘ -γ)]) #:transparent)
(define ⊤Γ (-Γ ∅ (hasheq) ∅))

;; Path condition tail is block and renaming information
(struct -γ ([callee : -ℬ]
            [fun : -s]
            [param->arg : (Listof (Pairof Symbol -s))]) #:transparent)

(: Γ+ : -Γ -s → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ (set-add φs s) as ts)]
        [else Γ]))

(: -Γ-with-aliases : -Γ Symbol -s → -Γ)
(define (-Γ-with-aliases Γ x s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ φs (hash-set as x s) ts)]
        [else Γ]))

(: Γ↓ : -Γ (℘ Symbol) → -Γ)
;; Restrict path-condition to given free variables
(define (Γ↓ Γ xs)

  (match-define (-Γ φs as γs) Γ)
  (define φs*
    (for*/set: : (℘ -e) ([φ φs] [φ* (in-value (e↓ φ xs))] #:when φ*)
      φ*))
  (define as*
    (for/hash : (HashTable Symbol -e) ([(x e) as] #:when (∋ xs x))
      (values x e)))
  (define γs*
    (for*/set: : (℘ -γ) ([γ γs]
                         #:when (s↓ (-γ-fun γ) xs)
                         #:when
                         (for/and : Boolean ([p (-γ-param->arg γ)])
                           (and (s↓ (cdr p) xs) #t))) ; force boolean :(
      γ))
  (-Γ φs* as* γs*))

(: canonicalize : (U -Γ (HashTable Symbol -e)) Symbol → -e)
;; Return an expression canonicalizing given variable in terms of lexically farthest possible variable(s)
(define (canonicalize X x)
  (cond [(-Γ? X) (canonicalize (-Γ-aliases X) x)]
        [else (hash-ref X x (λ () (-x x)))]))

;; Return an expression canonicalizing given expression in terms of lexically farthest possible variable(s)
(: canonicalize-e : (U -Γ (HashTable Symbol -e)) -e → -e)
(define (canonicalize-e X e)
  (cond [(-Γ? X) (canonicalize-e (-Γ-aliases X) e)]
        [else
         ((e/map (for/hash : (HashTable -e -e) ([(x e-x) X])
                   (values (-x x) e-x)))
          e)]))

(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (canonicalize-e (hash 'x (-@ '+ (list (-b 1) (-b 2)) -Λ))
                                (-@ '+ (list (-x 'x) (-x 'y)) -Λ))
                (-@ '+ (list (-@ '+ (list (-b 1) (-b 2)) -Λ) (-x 'y)) -Λ)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -𝒞 Natural)
(define-type Caller-Ctx Integer)
(define-values (𝒞∅ 𝒞+ decode-𝒞) ((inst make-indexed-set (Pairof -⟦e⟧ Caller-Ctx))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-α . ::= . ; For top-level definition and contract
            (-α.def -id)
            (-α.ctc -id)
            ; for binding
            (-α.x Symbol -𝒞)
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
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⟦e⟧ (-M -σ -ℬ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ))))
(define-type -⟦ℰ⟧ (-⟦e⟧ → -⟦e⟧))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Evaluation "unit" / "stack address"
(struct -ℬ ([code : -⟦e⟧] [env : -ρ] [cnd : -Γ] [hist : -𝒞]) #:transparent)

;; Continued evaluation
(struct -Co ([cont : -ℛ] [callee : -ℬ] [ans : (℘ -A)]) #:transparent)

;; Suspended, "intermediate" expression ℐ ≃ ℋ[ℬ]
(struct -ℐ ([hole : -ℋ] ; caller's hole
            [target : -ℬ] ; callee's context/address
            ) #:transparent)

;; Return point / continuation (deliberately distinct from `-ℋ`)
(struct -ℛ ([ctx : -ℬ] ; caller's context/address
            [hole : -ℋ] ; caller's continuation and path condition
            ) #:transparent)

(: -ℬ-with-Γ : -ℬ -Γ → -ℬ)
(define (-ℬ-with-Γ ℬ Γ)
  (cond [(eq? Γ (-ℬ-cnd ℬ)) ℬ] ; common case, keep old instance
        [else (match-define (-ℬ ⟦e⟧ ρ _ 𝒞) ℬ)
              (-ℬ ⟦e⟧ ρ Γ 𝒞)]))

(: -ℬ-with-ρ : -ℬ -ρ → -ℬ)
(define (-ℬ-with-ρ ℬ ρ)
  (cond [(eq? ρ (-ℬ-env ℬ)) ℬ]
        [else (match-define (-ℬ ⟦e⟧ _ Γ 𝒞) ℬ)
              (-ℬ ⟦e⟧ ρ Γ 𝒞)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Fixed
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-parameter set!-able? : (℘ (Pairof Symbol -e)) ∅)
(define-parameter σv : (HashTable -id -V) ((inst hash -id -V)))
(define-parameter σc : (HashTable -id -V) ((inst hash -id -V)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Collecting operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (for*/ans (clause ...) e ...)
  (for*/fold ([δσ : -Δσ ⊥σ] [ΓW : (℘ -ΓW) ∅] [ΓE : (℘ -ΓE) ∅] [ℐs : (℘ -ℐ) ∅])
             (clause ...)
    (define-values (δσ* ΓW* ΓE* ℐs*) (let () e ...))
    (values (⊔/m δσ δσ*) (∪ ΓW ΓW*) (∪ ΓE ΓE*) (∪ ℐs ℐs*))))

(define-syntax ⊔/ans
  (syntax-rules ()
    [(_) (⊥ans)]
    [(_ ans) ans]
    [(_ ans₁ ans ...)
     (let-values ([(δσ₁ Ws₁ Es₁ ℐs₁) ans₁]
                  [(δσ₂ Ws₂ Es₂ ℐs₂) (⊔/ans ans ...)])
       (values (⊔/m δσ₁ δσ₂) (∪ Ws₁ Ws₂) (∪ Es₁ Es₂) (∪ ℐs₁ ℐs₂)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Shorhands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (⊥ans) (values ⊥σ ∅ ∅ ∅))
(define-syntax-rule (with-Γ Γ e) (if Γ e (⊥ans)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α Vs) σ])
    `(,(show-α α) ↦ ,@(set-map Vs show-V))))

(define (show-s [s : -s]) (if s (show-e s) '∅))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ φs as ts) Γ)
  `(,(set-map φs show-e) ‖ ,(set-map ts show-γ)))

(define (show-Ξ [Ξ : -Ξ]) : (Listof Sexp)
  (for/list ([(ℬ ℛs) Ξ])
    `(,(show-ℬ ℬ) ↦ ,@(set-map ℛs show-ℛ))))

(define (show-M [M : -M]) : (Listof Sexp)
  (for/list ([(ℬ As) M])
    `(,(show-ℬ ℬ) ↦ ,@(set-map As show-A))))

(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-●) '●]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧ ρ _) `(Clo ,(show-formals xs) ,(show-⟦e⟧ ⟦e⟧) ,(show-ρ ρ))]
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
    [(-=>i γs (-Clo xs ⟦d⟧ _ _))
     (define cs : (Listof -s)
       (for/list ([γ : -α.dom γs])
         (match-define (-α.dom c) γ)
         (and (-e? c) c)))
     (match xs
       [(? list? xs)
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-s c)))
              (res ,xs ,(show-⟦e⟧ ⟦d⟧)))]
       [(-varargs xs₀ x)
        (define n (length xs₀))
        (match-define-values (γs₀ (list γ)) (split-at γs n))
        (match-define-values (cs₀ (list c)) (split-at cs n))
        `(->i ,(for/list : (Listof Sexp) ([x xs₀] [γ γs₀] [c cs₀])
                 `(,x ,(show-s c)))
              #:rest (,x ,(if (-e? γ) (show-e γ) (show-α γ)))
              (res ,(cons xs₀ x) ,(show-⟦e⟧ ⟦d⟧)))])]
    [(-St/C _ s αs)
     `(,(string->symbol (format "~a/c" (show-struct-info s))) ,@(map show-α αs))]
    [(-x/C (-α.x/c x)) `(recursive-contract ,(show-x/c x))]))

(define (show-A [A : -A])
  (match A
    [(-ΓW Γ W) `(W: ,(show-W W) ,(show-Γ Γ))]
    [(-ΓE Γ b) `(E: ,(show-blm b) ,(show-Γ Γ))]))

(define (show-W [W : -W]) : Sexp
  (match-define (-W Vs s) W)
  `(,@(map show-V Vs) @ ,(show-s s)))

(define (show-W¹ [W : -W¹]) : Sexp
  (match-define (-W¹ V s) W)
  `(,(show-V V) @ ,(show-s s)))

(define (show-blm [blm : -blm]) : Sexp
  (match-define (-blm l+ lo Cs Vs) blm)
  `(blame ,l+ ,lo ,(map show-V Cs) ,(map show-V Vs)))

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
  (match-define (-ℋ Γ f bnds ℰ) ℋ)
  `(ℋ ,(show-Γ Γ) ,(cons (show-s f) (show-bnds bnds)) ,(show-ℰ ℰ)))

(: show-bnds : (Listof (Pairof Symbol -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Symbol -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))

(define-values (show-⟦e⟧ show-⟦e⟧⁻¹ count-⟦e⟧) ((inst unique-sym -⟦e⟧) '⟦e⟧))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ ⟦e⟧ ρ Γ 𝒞) ℬ)
  `(ℬ ,(show-⟦e⟧ ⟦e⟧) ,(hash-keys ρ) ,(show-𝒞 𝒞) ,(show-Γ Γ)))

(define (show-Co [Co : -Co]) : Sexp
  (match-define (-Co ℛ ℬ ans) Co)
  `(Co ,(show-ℛ ℛ) ,(set-map ans show-A)))

(define (show-ℐ [ℐ : -ℐ]) : Sexp
  (match-define (-ℐ ℋ ℬ) ℐ)
  `(ℐ ,(show-ℋ ℋ) ,(show-ℬ ℬ)))

(define (show-ℛ [ℛ : -ℛ]) : Sexp
  (match-define (-ℛ ℬ ℋ) ℛ)
  `(ℛ ,(show-ℬ ℬ) ,(show-ℋ ℋ)))

(define (show-𝒞 [𝒞 : -𝒞]) : Symbol
  (string->symbol (format "𝒞~a" (n-sub 𝒞))))

(define-values (show-α show-α⁻¹ count-αs) ((inst unique-sym -α) 'α))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) ρ]) `(,x ↦ ,(show-α α))))

(define-values (show-γ show-γ⁻¹ count-γs) ((inst unique-sym -γ) 'γ))
