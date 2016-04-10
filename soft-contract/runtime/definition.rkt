#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/string
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Var-Name -α))
(define-type -Δρ -ρ)
(define ⊥ρ : -ρ (hasheq))
(define ρ@ : (-ρ Var-Name → -α) hash-ref)
(define ρ+ : (-ρ Var-Name -α → -ρ) hash-set)


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

(define-type -Ξ (HashTable -τ (℘ -ℛ)))
(define-type -ΔΞ -Ξ)
(define ⊥Ξ : -Ξ (hash))
(define Ξ@ : (-Ξ -τ → (℘ -ℛ)) m@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (HashTable -τ (℘ -A)))
(define-type -ΔM -M)
(define ⊥M : -M (hash))
(define M@ : (-M -τ → (℘ -A)) m@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . 'undefined
            -prim
            (-● (℘ -o))
            (-St -struct-info (Listof (U -α.fld -α.var-car -α.var-cdr)))
            (-Vector (Listof -α.idx))
            -Fn
            
            ;; Proxied higher-order values
            (-Ar [guard : #|ok, no rec|# -=>_] [v : -α] [ctx : Mon-Info])
            (-St* [info : -struct-info] [ctcs : (Listof (Option -α))] [val : -α.st] [ctx : Mon-Info])
            (-Vector/hetero [ctcs : (Listof -α)] [ctx : Mon-Info])
            (-Vector/homo [ctc : -α] [ctx : Mon-Info])
            
            -C)

(-Fn . ::= . (-Clo -formals -⟦e⟧ -ρ -Γ)
             (-Case-Clo (Listof (Pairof (Listof Var-Name) -⟦e⟧)) -ρ -Γ))

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean]
                    [l : (U -α.and/c-l -α.cnst)]
                    [r : (U -α.and/c-r -α.cnst)])
            (-Or/C [flat? : Boolean]
                   [l : (U -α.or/c-l -α.cnst)]
                   [r : (U -α.or/c-r -α.cnst)])
            (-Not/C (U -α.not/c -α.cnst))
            (-x/C [c : (U -α.x/c)])
            ;; Guards for higher-order values
            -=>_
            (-St/C [flat? : Boolean]
                   [info : -struct-info]
                   [fields : (Listof (U -α.struct/c -α.cnst))])
            (-Vectorof (U -α.vectorof -α.cnst))
            (-Vector/C (Listof (U -α.vector/c -α.cnst))))

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (Listof (U -α.dom -α.cnst))] [rng : -α])
              (-=>i [doms : (Listof (U -α.dom -α.cnst))] [mk-rng : -α])
              (-Case-> (Listof (Pairof (Listof -α.dom) -α.rng))))

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
            (-ℰ.def [l : Mon-Party] [addrs : (Listof (U -α.def -α.wrp))] [rhs : -ℰ])
            (-ℰ.dec -𝒾 -ℰ -ℓ)
            
            ;; Regular context
            '□
            (-ℰ.if Mon-Party -ℰ -⟦e⟧ -⟦e⟧)
            (-ℰ.@ Mon-Party -ℓ (Listof -W¹) -ℰ (Listof -⟦e⟧))
            (-ℰ.begin -ℰ (Listof -⟦e⟧))
            (-ℰ.begin0.v -ℰ (Listof -⟦e⟧))
            (-ℰ.begin0.e -W -ℰ (Listof -⟦e⟧))
            (-ℰ.let-values Mon-Party
                           (Listof (Pairof Var-Name -W¹))
                           (Pairof (Listof Var-Name) -ℰ)
                           (Listof (Pairof (Listof Var-Name) -⟦e⟧))
                           -⟦e⟧)
            (-ℰ.letrec-values Mon-Party
                              -Δρ
                              (Pairof (Listof Var-Name) -ℰ)
                              (Listof (Pairof (Listof Var-Name) -⟦e⟧))
                              -⟦e⟧)
            (-ℰ.set! Var-Name -ℰ)
            (-ℰ.μ/c Mon-Party -ℓ -ℰ)
            (-ℰ.-->.dom Mon-Party (Listof -W¹) -ℰ (Listof -⟦e⟧) -⟦e⟧ -ℓ)
            (-ℰ.-->.rng Mon-Party (Listof -W¹) -ℰ -ℓ)
            (-ℰ.-->i (Listof -W¹) -ℰ (Listof -⟦e⟧) -W¹ -ℓ)
            (-ℰ.case-> Mon-Party
                       -ℓ
                       (Listof (Listof -W¹))
                       (Listof -W¹) -ℰ (Listof -⟦e⟧)
                       (Listof (Listof -⟦e⟧)))
            (-ℰ.struct/c -struct-info (Listof -W¹) -ℰ (Listof -⟦e⟧) -ℓ)
            (-ℰ.mon.v Mon-Info -ℓ -ℰ [val : (U -⟦e⟧ -W¹)])
            (-ℰ.mon.c Mon-Info -ℓ [ctc : (U -⟦e⟧ -W¹)] -ℰ)

            ;; Hopefully can eliminate these eventually
            (-ℰ.wrap.st -struct-info (Listof -α) -α.st Mon-Info -ℰ)
            )

;; A "hole" ℋ is an evaluation context augmented with
;; caller's path condition and information for renaming callee's symbols
(struct -ℋ ([ctx : -ℒ] [bnd : -binding] [hole : -ℰ]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Symbolic value is either pure, refinable expression, or the conservative unrefinable `#f`
(-s . ::= . -e #f)

;; Path condition is set of (pure) expression known to have evaluated to non-#f
(struct -Γ ([facts : (℘ -e)]
            [aliases : (HashTable Var-Name -e)]
            [tails : (℘ -γ)]) #:transparent)

;; Path condition tail is callee block and renaming information,
;; also indicating whether the call raised a blame or not
(struct -γ ([callee : -τ] ; be careful with this. May build up infinitely
            [binding : -binding]
            [blm : (Option (Pairof Mon-Party Mon-Party))]) #:transparent)
(struct -binding ([fun : -s]
                  [params : (Listof Var-Name)]
                  [param->arg : (HashTable Var-Name -e)])
  #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq) ∅))

(: Γ+ : -Γ -s → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ (set-add φs s) as ts)]
        [else Γ]))

(: -Γ-with-aliases : -Γ Var-Name -s → -Γ)
(define (-Γ-with-aliases Γ x s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ φs (hash-set as x s) ts)]
        [else Γ]))

(: -binding-args : -binding → (Listof -s))
(define (-binding-args bnd)
  (match-define (-binding _ xs x->e) bnd)
  (for/list ([x xs]) (hash-ref x->e x #f)))

(: -binding-dom : -binding → (℘ Var-Name))
(define (-binding-dom bnd)
  (match-define (-binding _ _ x->e) bnd)
  (list->set (hash-keys x->e)))


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
            (-α.x Var-Name -𝒞)
            ; for struct field
            (-α.fld [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            ; for Cons/varargs
            (-α.var-car [pos : -ℓ] [ctx : -𝒞] [idx : Natural]) ; idx prevents infinite list 
            (-α.var-cdr [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [pos : -ℓ] [ctx : -𝒞])

            ;; for vector indices
            (-α.idx [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

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
            (-α.rng [pos : -ℓ] [ctx : -𝒞])

            -α.cnst)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⟦e⟧ (-M -σ -ℒ → (Values -Δσ (℘ -ΓW) (℘ -ΓE) (℘ -ℐ))))
(define-type -⟦ℰ⟧ (-⟦e⟧ → -⟦e⟧))
(define ⊥⟦e⟧ : -⟦e⟧ (λ (M σ ℒ) (values ⊥σ ∅ ∅ ∅)))
(define-values (remember-e! recall-e) ((inst make-memoeq -⟦e⟧ -e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(-τ . ::= . ;; Function body
            (-ℬ [code : -⟦e⟧] [ctx : -ℒ])
            ;; Contract monitoring
            (-ℳ [l³ : Mon-Info] [loc : -ℓ] [ctc : -W¹] [val : -W¹] [ctx : -ℒ]))

;; Local context
(struct -ℒ ([env : -ρ] [cnd : -Γ] [hist : -𝒞]) #:transparent)
(define ℒ∅ (-ℒ ⊥ρ ⊤Γ 𝒞∅))

;; Continued evaluation
(struct -Co ([cont : -ℛ] [callee : -τ] [ans : (℘ -A)]) #:transparent)

;; Suspended, "intermediate" expression ℐ ≃ ℋ[ℬ]
(struct -ℐ ([hole : -ℋ] ; caller's hole
            [target : -τ] ; callee's context/address
            ) #:transparent)

;; Return point / continuation (deliberately distinct from `-ℋ`)
(struct -ℛ ([ctx : -τ] ; caller's context/address
            [hole : -ℋ] ; caller's continuation and path condition
            ) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Fixed
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-parameter set!-able? : (℘ (Pairof Var-Name -e)) ∅)
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

(define-syntax-rule (for*/Δm (clause ...) e ...)
  (for*/fold ([δM : -ΔM ⊥M] [δΞ : -ΔΞ ⊥Ξ] [δσ : -Δσ ⊥σ])
             (clause ...)
    (define-values (δM* δΞ* δσ*) (let () e ...))
    (values (⊔/m δM δM*) (⊔/m δΞ δΞ*) (⊔/m δσ δσ*))))

(define-syntax ⊔/ans
  (syntax-rules ()
    [(_) (⊥ans)]
    [(_ ans) ans]
    [(_ ans₁ ans ...)
     (let-values ([(δσ₁ Ws₁ Es₁ ℐs₁) ans₁]
                  [(δσ₂ Ws₂ Es₂ ℐs₂) (⊔/ans ans ...)])
       (values (⊔/m δσ₁ δσ₂) (∪ Ws₁ Ws₂) (∪ Es₁ Es₂) (∪ ℐs₁ ℐs₂)))]))

(: ⊔/⟦e⟧ : -⟦e⟧ -⟦e⟧ → -⟦e⟧)
(define (⊔/⟦e⟧ ⟦e⟧₁ ⟦e⟧₂)
  (λ (M σ ℒ)
    (⊔/ans (⟦e⟧₁ M σ ℒ) (⟦e⟧₂ M σ ℒ))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Shorhands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (⊥ans) (values ⊥σ ∅ ∅ ∅))
(define-syntax-rule (with-Γ Γ e) (if Γ e (⊥ans)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α Vs) σ]
             #:when (or (-α.x? α) (-α.idx? α) (-α.st? α)))
    `(,(show-α α) ↦ ,@(set-map Vs show-V))))

(define (show-s [s : -s]) (if s (show-e s) '∅))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ φs as ts) Γ)
  `(,@(set-map φs show-e) ,@(set-map ts show-γ)))

(define (show-Ξ [Ξ : -Ξ]) : (Listof Sexp)
  (for/list ([(τ ℛs) Ξ])
    `(,(show-τ τ) ↦ ,@(set-map ℛs show-ℛ))))

(define (show-M [M : -M]) : (Listof Sexp)
  (for/list ([(τ As) M])
    `(,(show-τ τ) ↦ ,@(set-map As show-A))))

(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-● ps)
     (string->symbol (string-join (map symbol->string (cons '● (set-map ps show-o))) "_"))]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧ ρ _) `(λ ,(show-formals xs) ,(show-⟦e⟧ ⟦e⟧))]
    [(-Case-Clo clauses ρ Γ)
     `(case-lambda
       ,@(for/list : (Listof Sexp) ([clause clauses])
           (match-define (cons xs _) clause)
           `(,xs …)))]
    [(-Ar guard α _)
     (match α
       [(-α.def 𝒾) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
       [(-α.wrp 𝒾) (format-symbol "⟪~a⟫" (-𝒾-name 𝒾))]
       [_ `(,(show-V guard) ◃ ,(show-α α))])]
    [(-St s αs) `(,(show-struct-info s) ,@(map show-α αs))]
    [(-St* s γs α _)
     `(,(format-symbol "~a/wrapped" (show-struct-info s))
       ,@(for/list : (Listof Sexp) ([γ γs]) (if γ (show-α γ) '✓))
       ▹ ,(show-α α))]
    [(-Vector αs) `(vector ,@(map show-α αs))]
    [(-Vector/hetero γs _) `(vector/hetero ,@(map show-α γs))]
    [(-Vector/homo γ _) `(vector/homo ,(show-α γ))]
    [(-And/C _ l r) `(and/c ,(show-α l) ,(show-α r))]
    [(-Or/C _ l r) `(or/c ,(show-α l) ,(show-α r))]
    [(-Not/C γ) `(not/c ,(show-α γ))]
    [(-Vectorof γ) `(vectorof ,(show-α γ))]
    [(-Vector/C γs) `(vector/c ,@(map show-α γs))]
    [(-=> αs β) `(,@(map show-α αs) . -> . ,(show-α β))]
    [(-=>i γs α)
     (define cs : (Listof -s)
       (for/list ([γ : -α γs])
         (and (-e? γ) γ)))
     (define d : -s (and (-e? d) d))
     `(,@(map show-s cs) . ->i . ,(show-s d))]
    [(-Case-> cases)
     `(case->
       ,@(for/list : (Listof Sexp) ([kase cases])
           (match-define (cons αs β) kase)
           `(,@(map show-α αs) . -> . ,(show-α β))))]
    [(-St/C _ s αs)
     `(,(format-symbol "~a/c" (show-struct-info s)) ,@(map show-α αs))]
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
  (match* (Cs Vs)
    [('() (list (-b (? string? msg)))) `(error ,msg)] ;; HACK
    [(_ _) `(blame ,l+ ,lo ,(map show-V Cs) ,(map show-V Vs))]))

(: show-ℰ ([-ℰ] [Sexp] . ->* . Sexp))
(define (show-ℰ ℰ [in-hole '□])
  (let loop ([ℰ : -ℰ ℰ])
    (match ℰ
      [(-ℰ.def _ αs ℰ*)
       (define rhs (loop ℰ*))
       (match αs
         [(list α) `(define        ,(show-α α)      ,rhs)]
         [_        `(define-values ,(map show-α αs) ,rhs)])]
      [(-ℰ.dec 𝒾 ℰ* _)
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
      [(-ℰ.-->.dom _ Ws ℰ* ⟦c⟧s ⟦d⟧ _)
       `ℰ.-->.dom]
      [(-ℰ.-->.rng _ Ws ℰ* _)
       `ℰ.-->.rng]
      [(-ℰ.-->i Cs ℰ* cs (-W¹ (-Clo xs _ _ _) d) _)
       `(,@(map show-W¹ Cs) ,(loop ℰ*) ,@(map show-⟦e⟧ cs) ,(show-s d))]
      [(-ℰ.case-> _ _ _ _ _ _ _)
       `ℰ.case->]
      [(-ℰ.struct/c s Cs ℰ* cs _)
       `(,(format-symbol "~a/c" (-𝒾-name (-struct-info-id s)))
         ,@(map show-W¹ Cs)
         ,(loop ℰ*)
         ,(map show-⟦e⟧ cs))]
      [(-ℰ.mon.v _ _ ℰ* Val)
       `(mon ,(loop ℰ*) ,(if (-W¹? Val) (show-W¹ Val) (show-⟦e⟧ Val)))]
      [(-ℰ.mon.c _ _ Ctc ℰ*)
       `(mon ,(if (-W¹? Ctc) (show-W¹ Ctc) (show-⟦e⟧ Ctc)) ,(loop ℰ*))])))

(define (show-ℋ [ℋ : -ℋ])
  (match-define (-ℋ ℒ bnd ℰ) ℋ)
  `(ℋ ,(show-ℒ ℒ) ,(show-binding bnd) ,(show-ℰ ℰ)))

(: show-bnds : (Listof (Pairof Var-Name -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Var-Name -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))

(define show-⟦e⟧ : (-⟦e⟧ → Sexp)
  (let-values ([(⟦e⟧->symbol symbol->⟦e⟧ _) ((inst unique-sym -⟦e⟧) '⟦e⟧)])
    (λ (⟦e⟧)
      (cond [(recall-e ⟦e⟧) => show-e]
            [else (⟦e⟧->symbol ⟦e⟧)]))))

(define (show-τ [τ : -τ]) : Sexp
  (cond [(-ℬ? τ) (show-ℬ τ)]
        [else (show-ℳ τ)]))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ ⟦e⟧ ℒ) ℬ)
  `(ℬ ,(show-⟦e⟧ ⟦e⟧) ,(hash-keys (-ℒ-env ℒ))))

(define (show-ℳ [ℳ : -ℳ]) : Sexp
  (match-define (-ℳ l³ ℓ W-C W-V ℒ) ℳ)
  `(mon ,(show-W¹ W-C) ,(show-W¹ W-V) ,(show-ℒ ℒ)))

(define (show-ℒ [ℒ : -ℒ]) : Sexp
  (match-define (-ℒ ρ Γ 𝒞) ℒ)
  `(,@(show-ρ ρ) @ ,(show-Γ Γ) @,(show-𝒞 𝒞)))

(define (show-Co [Co : -Co]) : Sexp
  (match-define (-Co ℛ τ ans) Co)
  `(Co ,(show-ℛ ℛ) ,(set-map ans show-A)))

(define (show-ℐ [ℐ : -ℐ]) : Sexp
  (match-define (-ℐ ℋ τ) ℐ)
  `(ℐ ,(show-ℋ ℋ) ,(show-τ τ)))

(define (show-ℛ [ℛ : -ℛ]) : Sexp
  (match-define (-ℛ τ ℋ) ℛ)
  `(ℛ ,(show-τ τ) ,(show-ℋ ℋ)))

(define-parameter verbose? : Boolean #f)

(define (show-𝒞 [𝒞 : -𝒞]) : Sexp
  (cond [(verbose?)
         (for/list : (Listof Sexp) ([ctx : (Pairof -⟦e⟧ Caller-Ctx) (decode-𝒞 𝒞)])
           (match-define (cons ⟦e⟧ ℓ) ctx)
           `(,(show-⟦e⟧ ⟦e⟧) @ ,ℓ))]
        [else (format-symbol "𝒞~a" (n-sub 𝒞))]))

(define-values (show-α show-α⁻¹)
  (let-values ([(α->symbol symbol->α _) ((inst unique-sym -α) 'α)])
    (values
     (match-lambda
       [(? -e? α) (show-e α)]
       [(-α.x x 𝒞) (format-symbol "~a_~a" (show-Var-Name x) 𝒞)]
       [(? -α? α) (α->symbol α)])
     symbol->α)))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) ρ]) `(,(show-Var-Name x) ↦ ,(show-α α))))

(define show-γ : (-γ → Sexp)
  (let-values ([(show-γ show-γ⁻¹ count-γs) ((inst unique-sym -γ) 'γ)])
    (λ (γ)
      (cond [(verbose?)
             (match-define (-γ τ bnd blm) γ)
             `(,(show-τ τ) ‖ ,(show-binding bnd) ‖ ,blm)]
            [else (show-γ γ)]))))

(define (show-binding [bnd : -binding]) : (Listof Sexp)
  (match-define (-binding f xs x->e) bnd)
  (define bnds
    (for/list : (Listof Sexp) ([x xs])
      `(,x ↦ ,(show-s (hash-ref x->e x #f)))))
  (define fvs
    (for/list : (Listof Sexp) ([(x e) x->e] #:unless (member x xs))
      `(,x ↦ ,(show-e e))))
  `(,(show-s f) ,@bnds ‖ ,@fvs))
