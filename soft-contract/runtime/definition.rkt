#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/string
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt")
(require/typed racket/base
  [(hash-empty? ρ-empty?) (-ρ → Boolean)])
(provide ρ-empty?)


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
;; Store maps each address to value set and whether it may have been mutated

(struct -σr ([vals : (℘ -V)] [old? : Boolean]) #:transparent)
(define-type -σ (HashTable -α -σr))
;(define-type -Δσ -σ)
(define (⊥σ) : -σ (make-hash))
(define ⊥σr (-σr ∅ #f))

(: σ@ : -σ -α → (Values (℘ -V) Boolean))
(define (σ@ σ α)
  (match-define (-σr Vs old?) (hash-ref σ α (λ () (error 'σ@ "no address ~a" α))))
  (values Vs old?))

(: σ@ᵥ : -σ -α → (℘ -V))
(define (σ@ᵥ σ α)
  (define-values (Vs _) (σ@ σ α))
  Vs)

(: σr⊔ : -σr -V Boolean → -σr)
(define (σr⊔ σr V bind?)
  (match-define (-σr Vs bind?₀) σr)
  (-σr (set-add Vs V) (and bind?₀ bind?)))

(: σ⊔! : -σ -α -V Boolean → Void)
(define (σ⊔! σ α V bind?)
  (hash-update! σ α
                (λ ([σr₀ : -σr]) (σr⊔ σr₀ V bind?))
                (λ () ⊥σr)))

(define-syntax σ⊔*!
  (syntax-rules (↦)
    [(_ _) (void)]
    [(_ σ [α ↦ V b?] p ...)
     (begin
       (σ⊔!  σ α V b?)
       (σ⊔*! σ p ...))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -κ ([cont : -⟦k⟧!]      ; rest of computation waiting on answer
            [Γ : -Γ]          ; path-condition to use for rest of computation
            [𝒞 : -𝒞]         ; context of rest of computation
            [bnd : -binding]  ; mapping from caller's identifiers to callee's expressions
            )
  #:transparent)

(define-type -σₖ (HashTable -αₖ (℘ -κ)))
;(define-type -Δσₖ -σₖ)
(define (⊥σₖ) : -σₖ (make-hash))
(define σₖ@ : (-σₖ -αₖ → (℘ -κ)) m@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (HashTable -αₖ (℘ -ΓA)))
;(define-type -ΔM -M)
(define (⊥M) : -M (make-hash))
(define M@ : (-M -αₖ → (℘ -ΓA)) m@)


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
            (-Ar [guard : #|ok, no rec|# -=>_] [v : -α] [ctx : -l³])
            (-St* [info : -struct-info] [ctcs : (Listof (Option -α))] [val : -α.st] [ctx : -l³])
            (-Vector/hetero [ctcs : (Listof -α)] [ctx : -l³])
            (-Vector/homo [ctc : -α] [ctx : -l³])
            
            -C)

(-Fn . ::= . (-Clo -formals -⟦e⟧! -ρ -Γ)
             (-Case-Clo (Listof (Pairof (Listof Var-Name) -⟦e⟧!)) -ρ -Γ))

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
(-=>_ . ::= . (-=>  [doms : (Listof (U -α.dom -α.cnst))] [rng : -α] [pos : -ℓ])
              (-=>i [doms : (Listof (U -α.dom -α.cnst))] [mk-rng : -α] [pos : -ℓ])
              (-Case-> (Listof (Pairof (Listof -α.dom) -α.rng)) [pos : -ℓ]))

(struct -blm ([violator : -l] [origin : -l]
              [c : (Listof -V)] [v : (Listof -V)]) #:transparent)
(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -W ([Vs : (Listof -V)] [s : -s]) #:transparent)
(-A . ::= . -W -blm)
(struct -ΓA ([cnd : -Γ] [ans : -A]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Symbolic value is either pure, refinable expression, or the conservative unrefinable `#f`
(-s . ::= . -e #f)

;; Path condition is set of (pure) expression known to have evaluated to non-#f
;; Tails are addresses to other path-condition "chunks" from function calls,
;; each paired with appropriate renaming.
;; Tails are ordered from least to most recent application.
;; Order is important for effective rewriting. TODO obsolete, no longer need to preserve order
(struct -Γ ([facts : (℘ -e)]
            [aliases : (HashTable Var-Name -e)]
            [tails : (Listof -γ)]) #:transparent)

;; Path condition tail is callee block and renaming information,
;; also indicating whether the call raised a blame or not
(struct -γ ([callee : -αₖ] ; be careful with this. May build up infinitely
            [binding : -binding]
            [blm : (Option (Pairof -l -l))]) #:transparent)
(struct -binding ([fun : -s]
                  [params : (Listof Var-Name)]
                  [param->arg : (HashTable Var-Name -s)])
  #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq) '()))

(: Γ+ : -Γ -s * → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ . ss)
  (match-define (-Γ φs as ts) Γ)
  (define φs*
    (for/fold ([φs : (℘ -e) φs]) ([s ss] #:when s)
      (set-add φs s)))
  (-Γ φs* as ts))

(: -Γ-with-aliases : -Γ Var-Name -s → -Γ)
(define (-Γ-with-aliases Γ x s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ φs (hash-set as x s) ts)]
        [else Γ]))

(: -binding-dom : -binding → (℘ Var-Name))
(define (-binding-dom bnd)
  (match-define (-binding _ _ x->e) bnd)
  (for/unioneq : (℘ Var-Name) ([(x e) x->e])
     (set-add (if e (fv e) ∅eq) x)))

(: binding->s : -binding → -s)
(define (binding->s bnd)
  (match-define (-binding sₕ xs x->e) bnd)
  (cond
    [sₕ
     (define sₓs : (Listof -s)
       (for/list ([x xs])
         (hash-ref x->e x #f)))
     (cond [(andmap (inst values -s) sₓs)
            (-@ sₕ (cast sₓs (Listof -e)) +ℓ₀)]
           [else #f])]
    [else #f]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-new-subtype -𝒞 (+𝒞 Natural))
(define-values (𝒞∅ 𝒞+ decode-𝒞)
  (let-values ([(s∅ s+ decode) ((inst make-indexed-set (Pairof -⟦e⟧! -ℓ)))])
    (values (+𝒞 s∅)
            (λ ([𝒞 : -𝒞] [x : (Pairof -⟦e⟧! -ℓ)]) (+𝒞 (s+ 𝒞 x)))
            decode)))


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
            (-α.fld [id : -𝒾] [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
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
            (-α.fn [mon-pos : -ℓ] [guard-pos : -ℓ] [ctx : -𝒞])

            -α.cnst)

(define (α->s [α : -α]) : -s (and (-e? α) α))
(define (αs->ss [αs : (Listof -α)]) : (Listof -s) (map α->s αs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Continuations are not first class. No `σₖ` in arguments for now
(define-type -⟦e⟧! (-ρ -Γ -𝒞 -σ -σₖ -M -⟦k⟧! → (℘ -ς)))
(define-type -⟦k⟧! (-A -Γ -𝒞 -σ -σₖ -M       → (℘ -ς)))
(define-values (remember-e! recall-e) ((inst make-memoeq -⟦e⟧! -e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(-ς . ::= . #|block start |# (-ς↑ -αₖ -Γ -𝒞)
            #|block return|# (-ς↓ -αₖ -Γ -A))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(-αₖ . ::= . (-ℬ [exp : -⟦e⟧!] [env : -ρ])
             ;; Contract monitoring
            #;(-ℳ [l³ : -l³] [loc : -ℓ] [ctc : -W¹] [val : -W¹] [ctx : -ℒ])
            ;; Flat checking
            #;(-ℱ [l : -l] [loc : -ℓ] [ctc : -W¹] [val : -W¹] [ctx : -ℒ]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Shorhands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (with-Γ Γ e) (if Γ e ∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α σr) σ]
             #:unless (or (-α.def? α) (-α.wrp? α) (-e? α)))
    (match-define (-σr Vs _) σr)
    `(,(show-α α) ↦ ,@(set-map Vs show-V))))

(define (show-s [s : -s]) (if s (show-e s) '∅))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ φs _ γs) Γ)
  `(,@(set-map φs show-e) ,@(map show-γ γs)))

(define (show-σₖ [σₖ : -σₖ]) : (Listof Sexp)
  (for/list ([(αₖ κs) σₖ])
    `(,(show-αₖ αₖ) ↦ ,@(set-map κs show-κ))))

(define (show-M [M : -M]) : (Listof Sexp)
  (for/list ([(αₖ As) M])
    `(,(show-αₖ αₖ) ↦ ,@(set-map As show-ΓA))))

(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-● ps)
     (string->symbol (string-join (map symbol->string (cons '● (set-map ps show-o))) "_"))]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧! ρ _) `(λ ,(show-formals xs) ,(show-⟦e⟧! ⟦e⟧!))]
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
    [(-=> αs β _) `(,@(map show-α αs) . -> . ,(show-α β))]
    [(-=>i γs α _)
     (define cs : (Listof -s)
       (for/list ([γ : -α γs])
         (and (-e? γ) γ)))
     (define d : -s (and (-e? α) α))
     `(->i ,@(map show-s cs)
           ,(match d
              [(-λ (? list? xs) e) `(res ,xs ,(show-e e))]
              [_ (show-s d)]))]
    [(-Case-> cases _)
     `(case->
       ,@(for/list : (Listof Sexp) ([kase cases])
           (match-define (cons αs β) kase)
           `(,@(map show-α αs) . -> . ,(show-α β))))]
    [(-St/C _ s αs)
     `(,(format-symbol "~a/c" (show-struct-info s)) ,@(map show-α αs))]
    [(-x/C (-α.x/c ℓ)) `(recursive-contract ,(show-x/c ℓ))]))

(define (show-ΓA [ΓA : -ΓA]) : Sexp
  (match-define (-ΓA Γ A) ΓA)
  `(,(show-A A) ‖ ,(show-Γ Γ)))

(define (show-A [A : -A])
  (cond [(-W? A) (show-W A)]
        [else (show-blm A)]))

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

(: show-bnds : (Listof (Pairof Var-Name -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Var-Name -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))

(define show-⟦e⟧! : (-⟦e⟧! → Sexp)
  (let-values ([(⟦e⟧->symbol symbol->⟦e⟧! _) ((inst unique-sym -⟦e⟧!) '⟦e⟧)])
    (λ (⟦e⟧)
      (cond [(recall-e ⟦e⟧) => show-e]
            [else (⟦e⟧->symbol ⟦e⟧)]))))

(define (show-αₖ [αₖ : -αₖ]) : Sexp
  (cond [(-ℬ? αₖ) (show-ℬ αₖ)]
        [else     (error 'show-αₖ "~a" αₖ)]))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ ⟦e⟧! ρ) ℬ)
  `(ℬ ,(show-⟦e⟧! ⟦e⟧!) ,(show-ρ ρ)))

(define-parameter verbose? : Boolean #f)

(define (show-𝒞 [𝒞 : -𝒞]) : Sexp
  (cond [(verbose?)
         (for/list : (Listof Sexp) ([ctx : (Pairof -⟦e⟧! -ℓ) (decode-𝒞 𝒞)])
           (match-define (cons ⟦e⟧! ℓ) ctx)
           `(,(format-symbol "ℓ~a" (n-sub ℓ)) ↝ ,(show-⟦e⟧! ⟦e⟧!)))]
        [else (format-symbol "𝒞~a" (n-sub 𝒞))]))

(define-values (show-α show-α⁻¹)
  (let-values ([(α->symbol symbol->α _) ((inst unique-sym -α) 'α)])
    (values
     (match-lambda
       [(? -e? α) (show-e α)]
       [(-α.x x 𝒞) (format-symbol "~a_~a" (show-Var-Name x) (n-sub 𝒞))]
       [(? -α? α) (α->symbol α)])
     symbol->α)))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) ρ]) `(,(show-Var-Name x) ↦ ,(show-α α))))

(define show-γ : (-γ → Sexp)
  (let-values ([(show-γ show-γ⁻¹ count-γs) ((inst unique-sym -γ) 'γ)])
    (λ (γ)
      (cond [(verbose?)
             (match-define (-γ αₖ bnd blm) γ)
             `(,(show-αₖ αₖ) ‖ ,(show-binding bnd) ‖ ,blm)]
            [else (show-γ γ)]))))

(define (show-binding [bnd : -binding]) : (Listof Sexp)
  (match-define (-binding f xs x->e) bnd)
  (define bnds
    (for/list : (Listof Sexp) ([x xs])
      `(,(show-Var-Name x) ↦ ,(show-s (hash-ref x->e x #f)))))
  (define fvs
    (for/list : (Listof Sexp) ([(x e) x->e] #:unless (member x xs))
      `(,(show-Var-Name x) ↦ ,(show-s e))))
  `(,(show-s f) ,@bnds ‖ ,@fvs))

(define (show-κ [κ : -κ]) : Sexp
  (match-define (-κ ⟦k⟧ Γ 𝒞 bnd) κ)
  '⟦κ⟧)
