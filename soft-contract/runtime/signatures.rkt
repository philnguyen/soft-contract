#lang typed/racket/base

(provide (except-out (all-defined-out) -not/c)
         (rename-out [+not/c -not/c]))

(require racket/match
         racket/set
         syntax/parse/define
         typed/racket/unit
         bnf
         intern
         set-extras
         "../utils/bijection.rkt"
         "../ast/signatures.rkt"
         )

(define-type -ρ (Immutable-HashTable Symbol ⟪α⟫))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (Immutable-HashTable ⟪α⟫ -V^))
(define-type -σₖ (Immutable-HashTable -αₖ (℘ -⟦k⟧)))
(define-type -σₐ (Immutable-HashTable -αₖ (℘ (Listof -V^))))
(define-type -Ξ (Immutable-HashTable -H (Listof -αₖ)))

;; Grouped mutable references to stores
(struct -Σ ([σ : -σ] [σₖ : -σₖ] [σₐ : -σₐ] [Ξ : -Ξ]) #:mutable #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Runtime Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Abstract values
(-U . ::= . -prim
            (-● (℘ -h))
            (-St -𝒾 (Listof ⟪α⟫))
            (-Vector (Listof ⟪α⟫))
            (-Vector^ [content : ⟪α⟫] [length : #|restricted|# -V^])
            (-Hash^ [key : ⟪α⟫] [val : ⟪α⟫] [immutable? : Boolean])
            (-Set^ [elems : ⟪α⟫] [immutable? : Boolean])
            -Fn
            -h
            
            ;; Proxied higher-order values
            ;; Inlining the contract in the data definition is ok
            ;; because there's no recursion
            (-Ar [guard : -=>_] [v : ⟪α⟫] [ctx : -ctx])
            (-St* [guard : -St/C] [val : ⟪α⟫] [ctx : -ctx])
            (-Vector/guard [guard : (U -Vector/C -Vectorof)] [val : ⟪α⟫] [ctx : -ctx])
            (-Hash/guard [guard : -Hash/C] [val : ⟪α⟫] [ctx : -ctx])
            (-Set/guard [guard : -Set/C] [val : ⟪α⟫] [ctx : -ctx])
            (-Sealed ⟪α⟫)
            
            -C)

;; Abstract values + Symbolic Values
(-V . ::= . -U -t)
(define-type -V^ (℘ -V))

(-Fn . ::= . (-Clo -formals -⟦e⟧ -ρ)
             (-Case-Clo [cases : (Listof -Clo)])
             (-Fn● [arity : Arity] [tag : HV-Tag]))

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean] [l : -⟪α⟫ℓ] [r : -⟪α⟫ℓ])
            (-Or/C [flat? : Boolean] [l : -⟪α⟫ℓ] [r : -⟪α⟫ℓ])
            (-Not/C -⟪α⟫ℓ)
            (-One-Of/C (Setof Base))
            (-x/C [c : ⟪α⟫])
            ;; Guards for higher-order values
            -=>_
            (-St/C [flat? : Boolean] [id : -𝒾] [fields : (Listof -⟪α⟫ℓ)])
            (-Vectorof -⟪α⟫ℓ)
            (-Vector/C (Listof -⟪α⟫ℓ))
            (-Hash/C [key : -⟪α⟫ℓ] [val : -⟪α⟫ℓ])
            (-Set/C [elems : -⟪α⟫ℓ])
            ;; Seal
            (-Seal/C Symbol -H -l)

            )

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (-maybe-var -⟪α⟫ℓ)] [rng : (U (Listof -⟪α⟫ℓ) 'any)])
              (-=>i [doms : (Listof -⟪α⟫ℓ)]
                    [mk-rng : (Pairof -Clo ℓ)])
              (-∀/C (Listof Symbol) -⟦e⟧ -ρ)
              (-Case-> (Listof -=>)))

(struct -blm ([violator : -l]
              [origin : -l]
              [c : (Listof (U -U -v -h -V^))]
              [v : (Listof -V^)]
              [loc : ℓ]) #:transparent)
(-A . ::= . [#:old (Listof -V^)] -blm)

(struct -⟪α⟫ℓ ([addr : ⟪α⟫] [loc : ℓ]) #:transparent)
(HV-Tag . ::= . '† [#:old (Pairof -l -H)])

;; Convenient patterns
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

(define-syntax-rule (blm/simp l+ lo C V ℓ) (-blm l+ lo C V (strip-ℓ ℓ)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Monitoring contexts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -ctx ([pos : -l] [neg : -l] [src : -l] [loc : ℓ]) #:transparent)

(define ctx-neg : (-ctx → -ctx)
  (match-lambda
    [(-ctx l+ l- lo ℓ)
     (-ctx l- l+ lo ℓ)]))
(define ctx-with-ℓ : (-ctx ℓ → -ctx)
  (match-lambda**
   [((-ctx l+ l- lo _) ℓ) (-ctx l+ l- lo ℓ)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Symbols and Path Conditions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-φ . ::= . (-φ [condition : -Γ] [cache : -δσ]))
(define-type -δσ -σ)
(define-type -Γ (Immutable-HashTable -t (℘ -h)))

;; Symbolic names
(define-new-subtype -s (Integer->s Integer))
(-t . ::= . -s
            -b 
            (-t.@ -o (Listof -t)))

(-h . ::= . -o
            (-not/c (U -o -≡/c))
            (-</c -t)
            (-≤/c -t)
            (->/c -t)
            (-≥/c -t)
            (-≡/c -t)
            (-arity-includes/c Arity))
(-special-bin-o . ::= . '> '< '>= '<= '= 'equal? 'eqv? 'eq?)
(define-type Uni (Bij -t -t))

;; convenient syntax
(define-match-expander +not/c
  (syntax-rules () [(_ h) (-not/c h)])
  (syntax-rules () [(_ h) (match h
                            ['values 'not]
                            ['not 'values]
                            ['<= '>]
                            ['< '>=]
                            ['>= '<]
                            ['> '<=]
                            [(-</c t) (-≥/c t)]
                            [(-≤/c t) (->/c t)]
                            [(->/c t) (-≤/c t)]
                            [(-≥/c t) (-</c t)]
                            ['inexact? 'exact?]
                            ['exact? 'inexact?]
                            [p (-not/c p)])]))

(define-simple-macro (with-φ+/- ([(φ₁:id φ₂:id) e]) (~literal :) τ
                       #:true e₁
                       #:false e₂)
  (let-values ([(φs₁ φs₂) e])
    (∪ (for/union : (℘ τ) ([φ₁ (in-set φs₁)]) e₁)
       (for/union : (℘ τ) ([φ₂ (in-set φs₂)]) e₂))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⌊ρ⌋ (Immutable-HashTable Symbol (Listof ℓ)))
(define-type -edge.tgt (U (Pairof -⟦e⟧ -⌊ρ⌋) -o -h ℓ (-maybe-var ℓ) (Listof -edge.tgt) (℘ Base)))
(struct -edge ([tgt : -edge.tgt] [src : ℓ]) #:transparent)
(define-type -ℋ (Listof -edge))
(define-interner -H -ℋ
  #:intern-function-name -ℋ->-H
  #:unintern-function-name -H->-ℋ)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Cardinality (U 0 1 'N))

(-α . ::= . ; For wrapped top-level definition
            (-α.wrp -𝒾)
            ; for binding
            (-α.x Symbol -H)
            (-α.fv -H)
            ; for struct field
            (-α.fld [id : -𝒾] [loc : ℓ] [ctx : -H] [idx : Index])
            ; for Cons/varargs
            ; idx prevents infinite list
            (-α.var-car [loc : ℓ] [ctx : -H] [idx : (Option Natural)])
            (-α.var-cdr [loc : ℓ] [ctx : -H] [idx : (Option Natural)])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [mon-ctx : -ctx] [ctx : -H])

            ;; for vector indices
            (-α.idx [loc : ℓ] [ctx : -H] [idx : Natural])
            
            ;; for vector^ content
            (-α.vct [loc : ℓ] [ctx : -H])

            ;; for hash^ content
            (-α.hash.key [loc : ℓ] [ctx : -H])
            (-α.hash.val [loc : ℓ] [ctx : -H])

            ;; for set^ content
            (-α.set.elem [loc : ℓ] [ctx : -H])

            ;; for wrapped vector
            (-α.unvct [mon-ctx : -ctx] [ctx : -H])

            ;; for wrapped hash
            (-α.unhsh [mon-ctx : -ctx] [ctx : -H])

            ;; for wrapped set
            (-α.unset [mon-ctx : -ctx] [ctx : -H])

            ;; for contract components
            (-α.and/c-l [loc : ℓ] [ctx : -H])
            (-α.and/c-r [loc : ℓ] [ctx : -H])
            (-α.or/c-l [loc : ℓ] [ctx : -H])
            (-α.or/c-r [loc : ℓ] [ctx : -H])
            (-α.not/c [loc : ℓ] [ctx : -H])
            (-α.x/c Symbol -H)
            (-α.vector/c [loc : ℓ] [ctx : -H] [idx : Natural])
            (-α.vectorof [loc : ℓ] [ctx : -H])
            (-α.hash/c-key [loc : ℓ] [ctx : -H])
            (-α.hash/c-val [loc : ℓ] [ctx : -H])
            (-α.set/c-elem [loc : ℓ] [ctx : -H])
            (-α.struct/c [id : -𝒾] [loc : ℓ] [ctx : -H] [idx : Natural])
            (-α.dom [loc : ℓ] [ctx : -H] [idx : Natural])
            (-α.rst [loc : ℓ] [ctd : -H])
            (-α.rng [loc : ℓ] [ctx : -H] [idx : Natural])

            ;; for wrapped function
            (-α.fn [mon-ctx : -ctx] [ctx : -H])

            ;; For values wrapped in seals
            (-α.sealed Symbol -H) ; points to wrapped objects

            ;; HACK
            (-α.hv [tag : HV-Tag])
            (-α.mon-x/c Symbol -H -l)
            (-α.fc-x/c Symbol -H)
            -𝒾
            ;; tmp hack.
            ;; Only use this in the prim DSL where all values are finite
            ;; with purely syntactic components
            (-α.imm -U)
            ;; indirection for `listof` to keep in-sync with regular listof contracts
            (-α.imm-listof Symbol #|elem, ok with care|# -U ℓ)
            (-α.imm-ref-listof Symbol #|elem, ok with care|# -U ℓ)
            )

(-α.rec-ref . ::= . -α.x/c -α.imm-listof)

(define-interner ⟪α⟫ -α
  #:intern-function-name -α->⟪α⟫
  #:unintern-function-name ⟪α⟫->-α)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A computation returns set of next states
;; and may perform side effects widening mutable store(s)
(define-type -⟦e⟧ (-ρ -H -φ -Σ -⟦k⟧ → (℘ -ς)))
(define-type -⟦k⟧ (-A -H -φ -Σ     → (℘ -ς)))
(define-type -⟦f⟧ (ℓ (Listof -V^) -H -φ -Σ -⟦k⟧ → (℘ -ς)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(struct -ς ([ctx : -αₖ]) #:transparent)
#|block start |# (struct -ς↑ -ς () #:transparent)
#|block return|# (struct -ς↓ -ς ([ans : (Listof -V^)] [path : -φ]) #:transparent)
#|block raise |# (struct -ς! -ς ([blm : -blm]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(-αₖ . ::= . (-αₖ [instr : -H] [block : -Block] [path : -φ]))
(-Block . ::= . (-B [fun : -V] [args : (Listof -V^)] [loc : ℓ])
                (-M [blm-ctx : -ctx] [ctc : -V^] [val : -V^])
                (-F [l : -l] [loc : ℓ] [ctc : -V^] [val : -V^])
                (-HV [tag : HV-Tag]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Verification Result
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-R . ::= . '✓ '✗ '?)

(define-signature sat-result^
  ([not-R : (-R → -R)]
   [R⊔ : (-R -R * → -R)]
   [boolean->R : (Boolean → -R)]
   [R⊔* : (∀ (X) (X → -R) (Sequenceof X) → -R)]))

(define-signature env^
  ([⊥ρ : -ρ]
   [ρ@ : (-ρ Symbol → ⟪α⟫)]
   [ρ+ : (-ρ Symbol ⟪α⟫ → -ρ)]
   [-x-dummy : Symbol]))

(define-signature sto^
  ([⊥σ : -σ] 
   [alloc  : (-Σ -φ ⟪α⟫ -V^ → -φ)]
   [alloc* : (-Σ -φ (Listof ⟪α⟫) (Listof -V^) → -φ)]
   [mut!   : (-Σ -φ ⟪α⟫ -V^ → -φ)]
   [mut*!  : (-Σ -φ (Listof ⟪α⟫) (Listof -V^) → -φ)]
   [bind-args : (-Σ -ρ ℓ -H -φ -formals (Listof -V^) → (Values -ρ -φ))]
   [alloc-rest-args : ([-Σ ℓ -H -φ (Listof -V^)] [#:end -V] . ->* . (Values -V -φ))]
   [σ@ : ((U -Σ -σ) -δσ ⟪α⟫ → -V^)]
   [σ@/cache : ((U -Σ -σ) -φ ⟪α⟫ → (Listof (Pairof -V^ -φ)))]
   [σ@/list : ((U -Σ -σ) -δσ (Listof ⟪α⟫) → (Listof -V^))]
   [defined-at? : ((U -Σ -σ) -δσ ⟪α⟫ → Boolean)]
   [⟪α⟫ₒₚ : ⟪α⟫]
   [mutable? : (⟪α⟫ → Boolean)]
   [unalloc : (-σ -δσ -V → (℘ (Listof -V^)))]
   [unalloc-prefix : (-σ -δσ -V Natural → (℘ (Pairof (Listof -V^) -V)))]
   [⊥σₖ : -σₖ]
   [σₖ@ : ((U -Σ -σₖ) -αₖ → (℘ -⟦k⟧))]
   [⊥σₐ : -σₐ]
   [σₐ⊕! : (-Σ -φ -αₖ (Listof -V^) → (Listof -V^))] 
   [cardinality : (-σ -δσ ⟪α⟫ → Cardinality)]
   ))

(define-signature path^
  ([φ₀ : -φ]
   [φ-with-condition : (-φ -Γ → -φ)] 
   [t-names : (-t → (℘ Integer))]))

(define-signature summ^
  ([⊥Ξ : -Ξ]))

(define-signature val^
  ([fresh-sym! : (→ -s)]
   [C-flat? : (-V → Boolean)]
   [C^-flat? : (-V^ → Boolean)]
   [with-negative-party : (-l -V → -V)]
   [with-positive-party : (-l -V → -V)]
   [behavioral? : (-σ -δσ -V → Boolean)]
   [guard-arity : (-=>_ → Arity)]
   [blm-arity : (ℓ -l Arity (Listof -V^) → -blm)]
   [estimate-list-lengths : (-σ -δσ -V → (℘ (U #f Arity)))]
   ))

(define-signature unify^
  ([unify-Bl : (-Block -Block → (Option Uni))]
   [φ⊑/m? : (Uni -φ -φ → Boolean)]
   [rename-V^ : ((HashTable -t -t) -V^ → -V^)]
   [Γ+ : (-Γ (HashTable -t -t) -Γ → -Γ)]))

(define-signature instr^
  ([H∅ : -H]
   [H+ : (-H -edge → (Values -H Boolean))]
   [strip-fn : (-V → -edge.tgt)]
   [strip-ct : (-V → -edge.tgt)]
   [⌊ρ⌋ : (-ρ → -⌊ρ⌋)]
   ))

(define-signature pretty-print^
  ([show-ς : (-ς → Sexp)]
   [show-σ : (-σ → (Listof Sexp))]
   [show-h : (-h → Sexp)]
   [show-t : (-t → Sexp)]
   [show-Γ : (-Γ → (Listof Sexp))]
   [show-σₖ : (-σₖ → (Listof Sexp))]
   [show-blm-reason : ((U -U -v -h -V^) → Sexp)]
   [show-V : (-V → Sexp)]
   [show-V^ : (-V^ → Sexp)]
   [show-⟪α⟫ℓ : (-⟪α⟫ℓ → Symbol)]
   [show-⟪α⟫ℓs : ((Listof -⟪α⟫ℓ) → Sexp)]
   [show-A : (-A → Sexp)]
   [show-⟦e⟧ : (-⟦e⟧ → Sexp)]
   [show-αₖ : (-αₖ → Sexp)]
   [show-B : (-B → Sexp)]
   [show-edge : (-edge → Sexp)]
   [show-H : (-H → Sexp)]
   [show-⟪α⟫ : (⟪α⟫ → Sexp)]
   [show-ρ : (-ρ → (Listof Sexp))]
   [show-renaming : ((U Uni (HashTable -t -t)) → (Listof Sexp))]
   [dump-σ : ([-σ] [#:tag Any #:appendix? Boolean] . ->* . Void)]
   [remember-e! : (-e -⟦e⟧ → -⟦e⟧)]
   [recall-e : (-⟦e⟧ → (Option -e))]
   [verbose? : (Parameterof Boolean)]
   ))
