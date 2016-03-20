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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (HashTable -α (℘ -V)))
(define-type -Δσ -σ)
(define ⊥σ : -σ (hash))

(: σ@ : -σ -α → (℘ -V))
(define (σ@ σ α)
  (hash-ref σ α (λ () (error 'σ@ "non-existent address ~a" α))))

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
            (-Vector (Listof -α.idx))
            (-Clo -formals -⟦e⟧ -ρ -Γ)
            
            ;; Proxied higher-order values
            (-Ar [guard : #|ok, no rec|# -=>i] [v : (Pairof -α -s)] [ctx : Mon-Info])
            (-St* [info : -struct-info] [ctcs : (Listof (Option -α.struct/c))] [val : -α.st] [ctx : Mon-Info])
            (-Vector/hetero [ctcs : (Listof -α.vector/c)] [val : -α.vct] [ctx : Mon-Info])
            (-Vector/homo [ctc : -α.vectorof] [val : -α.vct] [ctx : Mon-Info])
            
            -C)

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean]
                    [l : (U -α.and/c-l -α.cnst)]
                    [r : (U -α.and/c-r -α.cnst)])
            (-Or/C [flat? : Boolean]
                   [l : (U -α.or/c-l -α.cnst)]
                   [r : (U -α.or/c-r -α.cnst)])
            (-Not/C (U -α.not/c -α.cnst))
            (-x/C [c : (U -α.x/c -α.cnst)])
            ;; Guards for higher-order values
            (-=>i [doms : (Listof (U -α.dom -α.cnst))] [#|ok, no recursion|# rng : -Clo])
            (-St/C [flat? : Boolean]
                   [info : -struct-info]
                   [fields : (Listof (U -α.struct/c -α.cnst))])
            (-Vectorof (U -α.vectorof -α.cnst))
            (-Vector/C (Listof (U -α.vector/c -α.cnst))))

(struct -blm ([violator : Mon-Party] [origin : Mon-Party]
              [c : (Listof -V)] [v : (Listof -V)]) #:transparent)
(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -W ([Vs : (Listof -V)] [s : -s]) #:transparent)
(struct -ΓW ([cnd : -Γ] [W : -W]) #:transparent)
(struct -ΓE ([cnd : -Γ] [blm : -blm]) #:transparent)
(-A . ::= . -ΓW -ΓE)
(-A* . ::= . (Listof -V) -blm)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Evaluation context
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-ℰ . ::= . ;; Different type of context. Hack for now. I may de-hack some day but not a big problem.
            (-ℰ.def [mod-name : Adhoc-Module-Path] [lhs : (Listof Symbol)] [rhs : -ℰ])
            (-ℰ.dec [name : -𝒾] [ctc : -ℰ])
            
            ;; Regular context
            '□
            (-ℰ.if Mon-Party -ℰ -⟦e⟧ -⟦e⟧)
            (-ℰ.@ Mon-Party -ℓ (Listof -W¹) -ℰ (Listof -⟦e⟧))
            (-ℰ.begin -ℰ (Listof -⟦e⟧))
            (-ℰ.begin0.v -ℰ (Listof -⟦e⟧))
            (-ℰ.begin0.e -W -ℰ (Listof -⟦e⟧))
            (-ℰ.let-values Mon-Party
                           (Listof (Pairof Symbol -W¹))
                           (Pairof (Listof Symbol) -ℰ)
                           (Listof (Pairof (Listof Symbol) -⟦e⟧))
                           -⟦e⟧)
            (-ℰ.letrec-values Mon-Party
                              -Δρ
                              (Pairof (Listof Symbol) -ℰ)
                              (Listof (Pairof (Listof Symbol) -⟦e⟧))
                              -⟦e⟧)
            (-ℰ.set! Symbol -ℰ)
            (-ℰ.μ/c Mon-Party Integer -ℰ)
            (-ℰ.-->i (Listof -W¹) -ℰ (Listof -⟦e⟧) -W¹ Integer)
            (-ℰ.struct/c -struct-info (Listof -W¹) -ℰ (Listof -⟦e⟧) Integer))

;; A "hole" ℋ is an evaluation context augmented with
;; caller's path condition and information for renaming callee's symbols
(struct -ℋ ([env : -ρ] [pc : -Γ] [f : -s] [param->arg : (Listof (Pairof Symbol -s))]
            [ctx : -ℰ]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Symbolic value is either pure, refinable expression, or the conservative unrefinable `#f`
(-s . ::= . -e #f)

;; Path condition is set of (pure) expression known to have evaluated to non-#f
(struct -Γ ([facts : (℘ -e)]
            [aliases : (HashTable Symbol -e)]
            [tails : (℘ -γ)]) #:transparent)

;; Path condition tail is block and renaming information
(struct -γ ([callee : -ℬ]
            [fun : -s]
            [param->arg : (Listof (Pairof Symbol -s))]) #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq) ∅))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -𝒞 Natural)
(define-type Caller-Ctx Integer)
(define-values (𝒞∅ 𝒞+ decode-𝒞) ((inst make-indexed-set (Pairof -⟦e⟧ Caller-Ctx))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(-α.cnst . ::= . -e)
(-α . ::= . ; For top-level definition and contract
            (-α.def -𝒾)
            (-α.wrp -𝒾)
            ; for binding
            (-α.x Symbol -𝒞)
            ; for struct field
            (-α.fld [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            ; for Cons/varargs
            (-α.var-car [pos : -ℓ] [ctx : -𝒞] [idx : Natural]) ; idx prevents infinite list 
            (-α.var-cdr [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [pos : -ℓ] [ctx : -𝒞])

            ;; for vector indices
            (-α.idx [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

            ;; for inner vector
            (-α.vct [pos : -ℓ] [ctx : -𝒞])

            ;; for contract components
            (-α.and/c-l [pos : -ℓ] [ctx : -𝒞])
            (-α.and/c-r [pos : -ℓ] [ctx : -𝒞])
            (-α.or/c-l [pos : -ℓ] [ctx : -𝒞])
            (-α.or/c-r [pos : -ℓ] [ctx : -𝒞])
            (-α.not/c [pos : -ℓ] [ctx : -𝒞])
            (-α.vector/c [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            (-α.vectorof [pos : -ℓ] [ctx : -𝒞])
            (-α.struct/c [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            (-α.x/c [pos : -ℓ])
            (-α.dom [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

            -α.cnst)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⟦e⟧ (-M -σ -ℬ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ))))
(define-type -⟦ℰ⟧ (-⟦e⟧ → -⟦e⟧))
(define-values (remember-e! recall-e) ((inst make-memoeq -⟦e⟧ -e)))


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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Fixed
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-parameter set!-able? : (℘ (Pairof Symbol -e)) ∅)
(define-parameter σv : (HashTable -𝒾 -V) ((inst hash -𝒾 -V)))
(define-parameter σc : (HashTable -𝒾 -V) ((inst hash -𝒾 -V)))


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
  `(,@(set-map φs show-e) ,@(set-map ts show-γ)))

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
    [(-Ar guard (cons α s) _) `(,(show-V guard) ◃ (,(show-α α) @ ,(show-s s)))]
    [(-St s αs) `(,(show-struct-info s) ,@(map show-α αs))]
    [(-St* s γs α _)
     `(,(string->symbol (format "~a/wrapped" (show-struct-info s)))
       ,@(for/list : (Listof Symbol) ([γ γs]) (if γ (show-α γ) '✓))
       ▹ ,(show-α α))]
    [(-Vector αs) `(vector ,@(map show-α αs))]
    [(-Vector/hetero γs α _) `(vector/hetero ,@(map show-α γs) ▹ ,(show-α α))]
    [(-Vector/homo γ α _) `(vector/homo ,(show-α γ) ▹ ,(show-α α))]
    [(-And/C _ l r) `(and/c ,(show-α l) ,(show-α r))]
    [(-Or/C _ l r) `(or/c ,(show-α l) ,(show-α r))]
    [(-Not/C γ) `(not/c ,(show-α γ))]
    [(-Vectorof γ) `(vectorof ,(show-α γ))]
    [(-Vector/C γs) `(vector/c ,@(map show-α γs))]
    [(-=>i γs (-Clo xs ⟦d⟧ _ _))
     (define cs : (Listof -s)
       (for/list ([γ : -α γs])
         (and (-e? γ) γ)))
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
    [(-x/C (-α.x/c ℓ)) `(recursive-contract ,(show-x/c ℓ))]))

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
      [(-ℰ.def _ xs ℰ*)
       (define rhs (loop ℰ*))
       (match xs
         [(list x) `(define        ,x  ,rhs)]
         [_        `(define-values ,xs ,rhs)])]
      [(-ℰ.dec 𝒾 ℰ*)
       `(provide/contract [,(-𝒾-name 𝒾) ,(loop ℰ*)])]
      
      ['□ in-hole]
      [(-ℰ.if _ ℰ* _ _) `(if ,(loop ℰ*) … …)]
      [(-ℰ.@ _ _ Ws ℰ* ⟦e⟧s) `(,@(map show-W¹ Ws) ,(loop ℰ*) ,(map (λ _ '…) ⟦e⟧s))]
      [(-ℰ.begin ℰ* ⟦e⟧s)
       `(begin ,(loop ℰ*) ,(format "…(~a)…" (length ⟦e⟧s)))]
      [(-ℰ.let-values _ xWs (cons xs ℰ*) xs-es e)
       `(let (,@(for/list : (Listof Sexp) ([xW xWs])
                  (match-define (cons x W) xW)
                  `(,x ,(show-W¹ W)))
              (,xs ,(loop ℰ*))
              ,@(for/list : (Listof Sexp) ([xs-e xs-es])
                  (match-define (cons x e) xs-e)
                  `(,xs ,(show-⟦e⟧ e))))
          ,(show-⟦e⟧ e))]
      [(-ℰ.letrec-values _ _ (cons xs ℰ*) xs-es e)
       `(letrec ((,xs ,(loop ℰ*))
                 ,@(for/list : (Listof Sexp) ([xs-e xs-es])
                     (match-define (cons xs e) xs-e)
                     `(,xs (show-⟦e⟧ e))))
          ,(show-⟦e⟧ e))]
      [(-ℰ.set! x ℰ*) `(set! ,x ,(loop ℰ*))]
      [(-ℰ.μ/c _ x ℰ*) `(μ/c ,x ,(loop ℰ*))]
      [(-ℰ.-->i Cs ℰ* cs (-W¹ (-Clo xs _ _ _) d) _)
       `(,@(map show-W¹ Cs) ,(loop ℰ*) ,@(map show-⟦e⟧ cs) ,(show-s d))]
      [(-ℰ.struct/c s Cs ℰ* cs _)
       `(,(format-symbol "~a/c" (-𝒾-name (-struct-info-id s)))
         ,@(map show-W¹ Cs)
         ,(loop ℰ*)
         ,(map show-⟦e⟧ cs))])))

(define (show-ℋ [ℋ : -ℋ])
  (match-define (-ℋ ρ Γ f bnds ℰ) ℋ)
  `(ℋ ,(show-Γ Γ) ,(cons (show-s f) (show-bnds bnds)) ,(show-ℰ ℰ)))

(: show-bnds : (Listof (Pairof Symbol -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Symbol -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))

(define-values (show-⟦e⟧ show-⟦e⟧⁻¹ count-⟦e⟧) ((inst unique-sym -⟦e⟧) 'e))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ ⟦e⟧ ρ Γ 𝒞) ℬ)
  `(ℬ ,(show-⟦e⟧ ⟦e⟧) ,(hash-keys ρ) ,(show-𝒞 𝒞) #;,(show-Γ Γ)))

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
