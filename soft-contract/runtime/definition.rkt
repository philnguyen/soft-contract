#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/string
         racket/splicing
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Symbol ⟪α⟫))
(define-type -Δρ -ρ)
(define ⊥ρ : -ρ (hasheq))
(define (ρ@ [ρ : -ρ] [x : Symbol]) : ⟪α⟫
  (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
(define ρ+ : (-ρ Symbol ⟪α⟫ → -ρ) hash-set)

;; HACK for distinguishing allocation contexts between 0-arg thunks,
;; which is important if the thunk returns different values (e.g. vector)
;; for different contexts
(define -x-dummy (+x! 'dummy))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Store maps each address to value set and whether it may have been mutated

(define-type -cardinality (U 0 1 'N))
(struct -σ ([m : (HashTable ⟪α⟫ (℘ -V))]
            [modified : (℘ ⟪α⟫)] ; addresses that may have been mutated
            [cardinality : (HashTable ⟪α⟫ -cardinality)]
            )
  #:transparent)

(: cardinality+ : -cardinality → -cardinality)
(define (cardinality+ c)
  (case c
    [(0) 1]
    [(1) 'N]
    [else 'N]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -κ ([cont : -⟦k⟧]    ; rest of computation waiting on answer
            [Γ : -Γ]        ; path-condition to use for rest of computation
            [⟪ℋ⟫ : -⟪ℋ⟫]    ; abstraction of call history
            [fun : -s]
            [args : (Listof -s)]
            )
  #:transparent)

(define-type -σₖ (HashTable -αₖ (℘ -κ)))

(define ⊥σₖ : -σₖ (hash))

(: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -κ))
(define (σₖ@ m αₖ)
  (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ →∅))

(: σₖ⊔ : -σₖ -αₖ -κ → -σₖ)
(define (σₖ⊔ σₖ αₖ κ)
  (hash-update σₖ αₖ (λ ([κs : (℘ -κ)]) (set-add κs κ)) →∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (HashTable -αₖ (℘ -ΓA)))
(define ⊥M : -M (hash))

(: M@ : (U -Σ -M) -αₖ → (℘ -ΓA))
(define (M@ m αₖ) (hash-ref (if (-Σ? m) (-Σ-M m) m) αₖ →∅))

(: M⊔ : -M -αₖ -Γ -A → -M)
(define (M⊔ M αₖ Γ A)
  (hash-update M αₖ (λ ([ΓAs : (℘ -ΓA)]) (set-add ΓAs (-ΓA Γ A))) →∅)
  #;(hash-update! M αₖ
                (λ ([ΓAs : (℘ -ΓA)])
                  (define check
                    (for/or : (U #f 'use-old -ΓA) ([ΓA₀ (in-set ΓAs)])
                      (match-define (-ΓA Γ₀ A₀) ΓA₀)
                      (and (equal? A₀ A)
                           (cond [(Γ⊆ Γ₀ Γ) 'use-old]
                                 [(Γ⊆ Γ Γ₀) ΓA₀]
                                 [else #f]))))
                  (case check
                    [(use-old) ΓAs]
                    [(#f) (set-add ΓAs (-ΓA Γ A))]
                    [else (set-add (set-remove ΓAs check) (-ΓA Γ A))]))
                →∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Grouped reference to mutable stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -Σ ([σ : -σ] [σₖ : -σₖ] [M : -M]) #:mutable #:transparent)

(: σₖ⊔! : -Σ -αₖ -κ → Void)
(define (σₖ⊔! Σ αₖ κ)
  (match-define (-Σ _ σₖ _) Σ)
  (set--Σ-σₖ! Σ (σₖ⊔ σₖ αₖ κ)))

(: M⊔! : -Σ -αₖ -Γ -A → Void)
(define (M⊔! Σ αₖ Γ A)
  (match-define (-Σ _ _ M) Σ)
  (set--Σ-M! Σ (M⊔ M αₖ Γ A)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . -prim
            (-● (℘ #|closed|# -v))
            (-St -𝒾 (Listof ⟪α⟫))
            (-Vector (Listof ⟪α⟫))
            (-Vector^ [content : ⟪α⟫] [length : #|restricted|# -V])
            -Fn
            
            ;; Proxied higher-order values
            ;; Inlining the contract in the data definition is ok
            ;; because there's no recursion
            (-Ar [guard : -=>_] [v : ⟪α⟫] [ctx : -l³])
            (-St* [guard : -St/C] [val : ⟪α⟫] [ctx : -l³])
            (-Vector/guard [guard : (U -Vector/C -Vectorof)] [val : ⟪α⟫] [ctx : -l³])
            
            -C)

(-Fn . ::= . (-Clo -formals -⟦e⟧ -ρ -Γ)
             (-Case-Clo (Listof (Pairof (Listof Symbol) -⟦e⟧)) -ρ -Γ))

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean]
                    [l : (Pairof ⟪α⟫ ℓ)]
                    [r : (Pairof ⟪α⟫ ℓ)])
            (-Or/C [flat? : Boolean]
                   [l : (Pairof ⟪α⟫ ℓ)]
                   [r : (Pairof ⟪α⟫ ℓ)])
            (-Not/C (Pairof ⟪α⟫ ℓ))
            (-x/C [c : ⟪α⟫])
            ;; Guards for higher-order values
            -=>_
            (-St/C [flat? : Boolean]
                   [id : -𝒾]
                   [fields : (Listof (Pairof ⟪α⟫ ℓ))])
            (-Vectorof (Pairof ⟪α⟫ ℓ))
            (-Vector/C (Listof (Pairof ⟪α⟫ ℓ))))

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (Listof (Pairof ⟪α⟫ ℓ))] [rng : (Pairof ⟪α⟫ ℓ)] [pos : ℓ])
              (-=>i [doms : (Listof (Pairof ⟪α⟫ ℓ))]
                    [mk-rng : (List -Clo -λ ℓ)]
                    [pos : ℓ])
              (-Case-> (Listof (Pairof (Listof ⟪α⟫) ⟪α⟫)) [pos : ℓ]))

(struct -blm ([violator : -l]
              [origin : -l]
              [c : (Listof (U -V -v))]
              [v : (Listof -V)]
              [loc : ℓ]) #:transparent)
(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -W ([Vs : (Listof -V)] [s : -s]) #:transparent)
(-A . ::= . -W -blm)
(struct -ΓA ([cnd : -Γ] [ans : -A]) #:transparent)

(define ⟪α⟫ℓ->⟪α⟫ (inst car ⟪α⟫ ℓ))


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
            [aliases : (HashTable Symbol -e)]
            [tails : (Listof -γ)]) #:transparent)

;; Path condition tail is callee block and renaming information,
;; also indicating whether the call raised a blame or not
(struct -γ ([callee : -αₖ] ; be careful with this. May build up infinitely
            [blm : (Option (Pairof -l -l))]
            [fun : -s]
            [args : (Listof -s)]) #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq) '()))

(: -Γ-with-aliases : -Γ Symbol -s → -Γ)
(define (-Γ-with-aliases Γ x s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ φs (hash-set as x s) ts)]
        [else Γ]))

(: Γ⊆ : -Γ -Γ → Boolean)
(define (Γ⊆ Γ₀ Γ₁)
  (match-define (-Γ φs₀ _ γs₀) Γ₀)
  (match-define (-Γ φs₁ _ γs₁) Γ₁)
  (and (⊆ φs₀ φs₁) (⊆ (list->set γs₀) (list->set γs₁))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes monitor + call site
(struct -ℒ ([mons : (℘ ℓ)] [app : ℓ]) #:transparent)

(define (ℒ-with-mon [ℒ : -ℒ] [ℓ : ℓ])
  (match-define (-ℒ ℓs ℓₐ) ℒ)
  (-ℒ (set-add ℓs ℓ) ℓₐ))

(struct -edge ([tgt : -⟦e⟧] [src : -ℒ]) #:transparent)
(define-type -ℋ (Listof (U -edge -ℒ)))
(define ℋ∅ : -ℋ '())

(: ℋ+ : -ℋ (U -edge -ℒ)  → -ℋ)
;; Add edge on top of call history.
;; If the target is already there, return the history chunk up to first time the target
;; is seen
(define (ℋ+ ℋ x)
  (define match? : ((U -edge -ℒ) → Boolean)
    (cond [(-ℒ? x) (λ (e) (equal? e x))]
          [(-edge? x)
           (define x.tgt (-edge-tgt x))
           (λ (e) (and (-edge? e) (eq? x.tgt (-edge-tgt e))))]))
  (define ?ℋ (memf match? ℋ))
  (if ?ℋ ?ℋ (cons x ℋ)))


;; The call history is passed around a lot and is part of address allocation
;; So it may be useful to intern for cheaper comparison
(define-interner -ℋ #:interned-type-name -⟪ℋ⟫)
(define ⟪ℋ⟫∅ (-ℋ->-⟪ℋ⟫ ℋ∅))

(: ⟪ℋ⟫+ : -⟪ℋ⟫ (U -edge -ℒ) → -⟪ℋ⟫)
(define (⟪ℋ⟫+ ⟪ℋ⟫ e) (-ℋ->-⟪ℋ⟫ (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(-α . ::= . ; For wrapped top-level definition
            (-α.wrp -𝒾)
            ; for binding
            (-α.x Symbol -⟪ℋ⟫)
            ; for struct field
            (-α.fld [id : -𝒾] [loc : -ℒ] [ctx : -⟪ℋ⟫] [idx : Natural])
            ; for Cons/varargs
            ; idx prevents infinite list
            (-α.var-car [loc : -ℒ] [ctx : -⟪ℋ⟫] [idx : (Option Natural)])
            (-α.var-cdr [loc : -ℒ] [ctx : -⟪ℋ⟫] [idx : (Option Natural)])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [loc : -ℒ] [ctx : -⟪ℋ⟫])

            ;; for vector indices
            (-α.idx [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            
            ;; for vector^ content
            (-α.vct [loc : ℓ] [ctx : -⟪ℋ⟫])

            ;; for wrapped vector
            (-α.unvct [loc : -ℒ] [ctx : -⟪ℋ⟫])

            ;; for contract components
            (-α.and/c-l [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.and/c-r [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.or/c-l [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.or/c-r [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.not/c [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.vector/c [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.vectorof [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.struct/c [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.x/c Symbol)
            (-α.dom [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.rng [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.fn [mon-loc : -ℒ] [ctx : -⟪ℋ⟫])

            (-α.hv) ; hack

            -e)

(define (α->s [α : -α]) (and (-e? α) α))
(define (αs->ss [αs : (Listof -α)]) (map α->s αs))

(define-interner -α #:interned-type-name ⟪α⟫)
(define (⟪α⟫->s [⟪α⟫ : ⟪α⟫]) (α->s (⟪α⟫->-α ⟪α⟫)))
(define (⟪α⟫s->ss [⟪α⟫s : (Listof ⟪α⟫)]) (map ⟪α⟫->s ⟪α⟫s))
(define ⟪α⟫ₕᵥ (-α->⟪α⟫ (-α.hv)))

(define ⊥σ (-σ (hasheq ⟪α⟫ₕᵥ ∅) ∅eq (hasheq)))
(define (⊥Σ) (-Σ ⊥σ ⊥σₖ ⊥M))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cache for address lookup in local block
(define-type -$ (HashTable -e -V))
(define $∅ : -$ (hash))
(define ($@ [$ : -$] [s : -s]) : (Option -V)
  (and s (hash-ref $ s #f)))

(define ($+ [$ : -$] [s : -s] [V : -V]) : -$
  (if s (hash-set $ s V) $))

;; A computation returns set of next states
;; and may perform side effects widening mutable store(s)
(define-type -⟦e⟧ (-ρ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))
(define-type -⟦k⟧ (-A -$ -Γ -⟪ℋ⟫ -Σ     → (℘ -ς)))
(define-values (remember-e! recall-e) ((inst make-memoeq -⟦e⟧ -e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(-ς . ::= . #|block start |# (-ς↑ -αₖ -Γ -⟪ℋ⟫)
            #|block return|# (-ς↓ -αₖ -Γ -A))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(-αₖ . ::= . (-ℬ [var : -formals] [exp : -⟦e⟧] [env : -ρ])
     ;; Contract monitoring
     (-ℳ [var : Symbol] [l³ : -l³] [loc : -ℒ] [ctc : -V] [val : ⟪α⟫])
     ;; Flat checking
     (-ℱ [var : Symbol] [l : -l] [loc : -ℒ] [ctc : -V] [val : ⟪α⟫])
     ;; Havoc
     (-ℋ𝒱)
     )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Convenient paterns
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-match-expander -Cons
  (syntax-rules () [(_ αₕ αₜ) (-St (== -𝒾-cons) (list αₕ αₜ))])
  (syntax-rules () [(_ αₕ αₜ) (-St -𝒾-cons      (list αₕ αₜ))]))
(define-match-expander -Cons*
  (syntax-rules () [(_ α) (-St* (-St/C _ (== -𝒾-cons) _) α _)]))
(define-match-expander -Box
  (syntax-rules () [(_ α) (-St (== -𝒾-box) (list α))])
  (syntax-rules () [(_ α) (-St -𝒾-box      (list α))]))
(define-match-expander -Box*
  (syntax-rules () [(_ α) (-St* (-St/C _ (== -𝒾-box) _) α _)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-ς [ς : -ς]) : Sexp
  (match ς
    [(-ς↑ αₖ Γ ⟪ℋ⟫) `(ev: ,⟪ℋ⟫ ,(show-αₖ αₖ) ‖ ,@(show-Γ Γ))]
    [(-ς↓ αₖ Γ A)  `(rt: ,(show-αₖ αₖ) ,(show-A A) ‖ ,@(show-Γ Γ))]))

(define (show-Σ [Σ : -Σ]) : (Values (Listof Sexp) (Listof Sexp) (Listof Sexp))
  (match-define (-Σ σ σₖ M) Σ)
  (values (show-σ σ) (show-σₖ σₖ) (show-M M)))

(define (show-σ [σ : (U -σ (HashTable ⟪α⟫ (℘ -V)))]) : (Listof Sexp)
  (cond [(-σ? σ) (show-σ (-σ-m σ))]
        [else
         (for*/list : (Listof Sexp) ([(⟪α⟫ᵢ Vs) σ]
                                     [α (in-value (⟪α⟫->-α (cast #|FIXME TR|# ⟪α⟫ᵢ ⟪α⟫)))])
           `(,(show-⟪α⟫ (cast #|FIXME TR|# ⟪α⟫ᵢ ⟪α⟫)) ↦ ,@(set-map Vs show-V)))]))

(define (show-s [s : -s]) (if s (show-e s) '∅))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ φs _ γs) Γ)
  `(,@(set-map φs show-e) ,@(map show-γ γs)))

(define (show-σₖ [σₖ : (U -σₖ (HashTable -αₖ (℘ -κ)))]) : (Listof Sexp)
  (for/list ([(αₖ κs) σₖ])
    `(,(show-αₖ αₖ) ↦ ,@(set-map κs show-κ))))

(define (show-M [M : (U -M (HashTable -αₖ (℘ -ΓA)))]) : (Listof Sexp)
  (for/list ([(αₖ As) M])
    `(,(show-αₖ αₖ) ↦ ,@(set-map As show-ΓA))))

(define show-V-or-v : ((U -V -v) → Sexp)
  (match-lambda
    [(? -V? V) (show-V V)]
    [(? -v? v) (show-e v)]))

(define (show-V [V : -V]) : Sexp
  (match V
    [(-b b) (show-b b)]
    [(-● ps)
     (string->symbol
      (string-join
       (for/list : (Listof String) ([p ps])
         (format "_~a" (show-e p)))
       ""
       #:before-first "●"))]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧ ρ _) `(λ ,(show-formals xs) ,(show-⟦e⟧ ⟦e⟧))]
    [(-Case-Clo clauses ρ Γ)
     `(case-lambda
       ,@(for/list : (Listof Sexp) ([clause clauses])
           (match-define (cons xs _) clause)
           `(,xs …)))]
    [(-Ar guard α _)
     (match α
       [(? -𝒾? 𝒾) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
       [(-α.wrp 𝒾) (format-symbol "⟪~a⟫" (-𝒾-name 𝒾))]
       [_ `(,(show-V guard) ◃ ,(show-⟪α⟫ α))])]
    [(-St 𝒾 αs) `(,(-𝒾-name 𝒾) ,@(map show-⟪α⟫ αs))]
    [(-St* (-St/C _ 𝒾 γℓs) α _)
     `(,(format-symbol "~a/wrapped" (-𝒾-name 𝒾))
       ,@(for/list : (Listof Sexp) ([γℓ γℓs]) (if γℓ (show-⟪α⟫ℓ γℓ) '✓))
       ▹ ,(show-⟪α⟫ α))]
    [(-Vector αs) `(vector ,@(map show-⟪α⟫ αs))]
    [(-Vector^ α n) `(vector^ ,(show-⟪α⟫ α) ,(show-V n))]
    [(-Vector/guard grd _ _)
     (match grd
       [(-Vector/C γs) `(vector/hetero ,@(map show-⟪α⟫ℓ γs))]
       [(-Vectorof γ) `(vector/homo ,(show-⟪α⟫ℓ γ))])]
    [(-And/C _ l r) `(and/c ,(show-⟪α⟫ (car l)) ,(show-⟪α⟫ (car r)))]
    [(-Or/C _ l r) `(or/c ,(show-⟪α⟫ (car l)) ,(show-⟪α⟫ (car r)))]
    [(-Not/C γ) `(not/c ,(show-⟪α⟫ (car γ)))]
    [(-Vectorof γ) `(vectorof ,(show-⟪α⟫ (car γ)))]
    [(-Vector/C γs) `(vector/c ,@(map show-⟪α⟫ (map ⟪α⟫ℓ->⟪α⟫ γs)))]
    [(-=> αs β _) `(,@(map show-⟪α⟫ℓ αs) . -> . ,(show-⟪α⟫ℓ β))]
    [(-=>i γs (list (-Clo _ ⟦e⟧ _ _) (-λ xs d) _) _)
     `(->i ,@(map show-⟪α⟫ℓ γs)
           ,(match xs
              [(? list? xs) `(res ,xs ,(show-e d))]
              [_ (show-e d)]))]
    [(-Case-> cases _)
     `(case->
       ,@(for/list : (Listof Sexp) ([kase cases])
           (match-define (cons αs β) kase)
           `(,@(map show-⟪α⟫ αs) . -> . ,(show-⟪α⟫ β))))]
    [(-St/C _ 𝒾 αs)
     `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(map show-⟪α⟫ (map ⟪α⟫ℓ->⟪α⟫ αs)))]
    [(-x/C ⟪α⟫) `(recursive-contract ,(show-⟪α⟫ ⟪α⟫))]))

(define (show-⟪α⟫ℓ [⟪α⟫ℓ : (Pairof ⟪α⟫ ℓ)]) : Symbol
  (match-define (cons ⟪α⟫ ℓ) ⟪α⟫ℓ)
  (define α (⟪α⟫->-α ⟪α⟫))
  (string->symbol
   (format "~a~a" (if (-e? α) (show-e α) (show-⟪α⟫ ⟪α⟫)) (n-sup ℓ))))

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
  (match-define (-blm l+ lo Cs Vs ℓ) blm)
  (match* (Cs Vs)
    [('() (list (-b (? string? msg)))) `(error ,msg)] ;; HACK
    [(_ _) `(blame ,l+ ,lo ,(map show-V-or-v Cs) ,(map show-V Vs) ,(show-ℓ ℓ))]))

(: show-bnds : (Listof (Pairof Symbol -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Symbol -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))

(define show-⟦e⟧ : (-⟦e⟧ → Sexp)
  (let-values ([(⟦e⟧->symbol symbol->⟦e⟧ _) ((inst unique-sym -⟦e⟧) '⟦e⟧)])
    (λ (⟦e⟧)
      (cond [(recall-e ⟦e⟧) => show-e]
            [else (⟦e⟧->symbol ⟦e⟧)]))))

(define (show-αₖ [αₖ : -αₖ]) : Sexp
  (cond [(-ℬ? αₖ) (show-ℬ αₖ)]
        [(-ℳ? αₖ) (show-ℳ αₖ)]
        [(-ℱ? αₖ) (show-ℱ αₖ)]
        [(-ℋ𝒱? αₖ) 'ℋ𝒱]
        [else     (error 'show-αₖ "~a" αₖ)]))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ xs ⟦e⟧ ρ) ℬ)
  (match xs
    ['() `(ℬ ()                 ,(show-⟦e⟧ ⟦e⟧) ,(show-ρ ρ))]
    [_   `(ℬ ,(show-formals xs) …               ,(show-ρ ρ))]))

(define (show-ℳ [ℳ : -ℳ]) : Sexp
  (match-define (-ℳ x l³ ℓ C V) ℳ)
  `(ℳ ,x ,(show-V C) ,(show-⟪α⟫ V)))

(define (show-ℱ [ℱ : -ℱ]) : Sexp
  (match-define (-ℱ x l ℓ C V) ℱ)
  `(ℱ ,x ,(show-V C) ,(show-⟪α⟫ V)))

(define-parameter verbose? : Boolean #f)

(define (show-⟪ℋ⟫ [⟪ℋ⟫ : -⟪ℋ⟫]) : Sexp
  (if (verbose?)
      (show-ℋ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫))
      ⟪ℋ⟫))
(define (show-ℋ [ℋ : -ℋ]) : (Listof Sexp)
  (for/list ([e ℋ])
    (match e
      [(-edge ⟦e⟧ ℒ)
       `(,(show-ℒ ℒ) ↝ ,(show-⟦e⟧ ⟦e⟧))]
      [(? -ℒ? ℒ) (show-ℒ ℒ)])))

(define show-ℒ : (-ℒ → Sexp)
  (let-values ([(ℒ->symbol symbol->ℒ _) ((inst unique-sym -ℒ) 'ℒ)])
    (λ (ℒ)
      (cond [(verbose?)
             (match-define (-ℒ ℓs ℓ) ℒ)
             `(ℒ ,(set->list ℓs) ,ℓ)]
            [else (ℒ->symbol ℒ)]))))

(define (show-⟪α⟫ [⟪α⟫ : ⟪α⟫]) : Sexp
  (define α (⟪α⟫->-α ⟪α⟫))
  (match (⟪α⟫->-α ⟪α⟫)
    [(-α.x x ⟪ℋ⟫) (format-symbol "~a_~a" x (n-sub ⟪ℋ⟫))]
    [(? -e? e) (show-e e)]
    [_ (format-symbol "α~a" (n-sub ⟪α⟫))]))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x ⟪α⟫ₓ) ρ] #:unless (equal? x -x-dummy))
    `(,x ↦ ,(show-⟪α⟫ (cast #|FIXME TR|# ⟪α⟫ₓ ⟪α⟫)))))

(define show-γ : (-γ → Sexp)
  (let-values ([(show-γ show-γ⁻¹ count-γs) ((inst unique-sym -γ) 'γ)])
    (λ (γ)
      (match-define (-γ αₖ blm? sₕ sₓs) γ)
      (cond [(verbose?)
             `(,(show-αₖ αₖ) ‖ (,(show-s sₕ) ,@(map show-s sₓs)) ‖ ,blm?)]
            [else
             `(,(if blm? '⇓ '@) ,(show-s sₕ) ,@(map show-s sₓs))]))))

(define (show-κ [κ : -κ]) : Sexp
  (match-define (-κ ⟦k⟧ Γ ⟪ℋ⟫ sₕ sₓs) κ)
  `(,(show-s sₕ) ,@(map show-s sₓs) ‖ ,(show-Γ Γ) @ ,(show-⟪ℋ⟫ ⟪ℋ⟫)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; TMP HACKS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TMP hack for part of root set from stack frames
(splicing-let ([m ((inst make-hasheq -⟦k⟧ (℘ ⟪α⟫)))])
  
  (define (add-⟦k⟧-roots! [⟦k⟧ : -⟦k⟧] [αs : (℘ ⟪α⟫)]) : Void
    (hash-update! m ⟦k⟧ (λ ([αs₀ : (℘ ⟪α⟫)]) (∪ αs₀ αs)) →∅eq))
  
  ;; Return the root set spanned by the stack chunk for current block
  (define (⟦k⟧->roots [⟦k⟧ : -⟦k⟧])
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αs "nothing for ~a" ⟦k⟧)))))

;; TMP hack for mapping stack to stack address to return to
(splicing-let ([m ((inst make-hasheq -⟦k⟧ -αₖ))])

  (define (set-⟦k⟧->αₖ! [⟦k⟧ : -⟦k⟧] [αₖ : -αₖ]) : Void
    (hash-update! m ⟦k⟧
                  (λ ([αₖ₀ : -αₖ]) ; just for debugging
                    (assert (equal? αₖ₀ αₖ))
                    αₖ₀)
                  (λ () αₖ)))
  
  (define (⟦k⟧->αₖ [⟦k⟧ : -⟦k⟧]) : -αₖ
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αₖ "nothing for ~a" ⟦k⟧)))))
