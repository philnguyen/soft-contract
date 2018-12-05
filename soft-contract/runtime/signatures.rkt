#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         syntax/parse/define
         typed/racket/unit
         bnf
         intern
         set-extras
         "../ast/signatures.rkt"
         )

(define-type -ρ (Immutable-HashTable Symbol ⟪α⟫))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (Immutable-HashTable ⟪α⟫ (℘ -V)))
(define-type -σₖ (Immutable-HashTable -αₖ (℘ -κ)))
(define-type -𝒜 (Immutable-HashTable ⟪α⟫ (℘ -loc)))
(define-type -Ξ (Immutable-HashTable -αₖ:ctx (℘ -αₖ:pth)))

(struct -κ ([rest : -⟦k⟧]) #:transparent)
(struct -κ.rt -κ ([dom : (℘ (U Symbol ℓ))] [pc : -Γ] [ans : -?t] [looped? : Boolean] [bnds : (Immutable-HashTable Symbol -t)]) #:transparent)

;; Grouped mutable references to stores
(struct -Σ ([σ : -σ] [σₖ : -σₖ] [𝒜 : -𝒜] [Ξ : -Ξ]) #:mutable #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Runtime Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . -prim
            (-● (℘ -h))
            (-St -𝒾 (Listof ⟪α⟫))
            (-Vector (Listof ⟪α⟫))
            (-Vector^ [content : ⟪α⟫] [length : #|restricted|# -V])
            (-Hash^ [key : ⟪α⟫] [val : ⟪α⟫] [immutable? : Boolean])
            (-Set^ [elems : ⟪α⟫] [immutable? : Boolean])
            -Fn
            
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

(-Fn . ::= . (-Clo -formals -⟦e⟧ -ρ -Γ)
             (-Case-Clo [cases : (Listof -Clo)])
             (-Fn● [arity : Arity] [tag : HV-Tag]))

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean]
                    [l : -⟪α⟫ℓ]
                    [r : -⟪α⟫ℓ])
            (-Or/C [flat? : Boolean]
                   [l : -⟪α⟫ℓ]
                   [r : -⟪α⟫ℓ])
            (-Not/C -⟪α⟫ℓ)
            (-One-Of/C (Setof Base))
            (-x/C [c : ⟪α⟫])
            ;; Guards for higher-order values
            -=>_
            (-St/C [flat? : Boolean]
                   [id : -𝒾]
                   [fields : (Listof -⟪α⟫ℓ)])
            (-Vectorof -⟪α⟫ℓ)
            (-Vector/C (Listof -⟪α⟫ℓ))
            (-Hash/C [key : -⟪α⟫ℓ] [val : -⟪α⟫ℓ])
            (-Set/C [elems : -⟪α⟫ℓ])
            ;; Seal
            (-Seal/C Symbol -H -l)

            ;;
            ->/c -≥/c -</c -≤/c -≢/c
            )

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (-maybe-var -⟪α⟫ℓ)] [rng : (U (Listof -⟪α⟫ℓ) 'any)])
              (-=>i [doms : (Listof -⟪α⟫ℓ)]
                    [mk-rng : (List -Clo -λ ℓ)])
              (-∀/C (Listof Symbol) -⟦e⟧ -ρ)
              (-Case-> (Listof -=>)))

(struct -blm ([violator : -l]
              [origin : -l]
              [c : (Listof (U -V -v -h))]
              [v : (Listof -V)]
              [loc : ℓ]) #:transparent)
(struct -W¹ ([V : -V] [t : -?t]) #:transparent)
(struct -W ([Vs : (Listof -V)] [t : -?t]) #:transparent)
(-A . ::= . -W -blm)

(struct -⟪α⟫ℓ ([addr : ⟪α⟫] [loc : ℓ]) #:transparent)
(HV-Tag . ::= . '† [#:reuse (Pairof -l -H)])

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

(-loc . ::= . ;; references
              Symbol -𝒾
              ;; struct field or vector access with concrete offset
              (-loc.offset (U -𝒾 Symbol) Index -t)
              )

(define-type -$ (Immutable-HashTable -loc -t))
(define-type -δ$ (Immutable-HashTable -loc -?t))

;; Path condition is set of terms known to have evaluated to non-#f
;; It also maintains a "canonicalized" symbolic name for each variable
(define-type -Γ (℘ -t))

;; First order term for use in path-condition
(-t . ::= . (-t.x Symbol)
            -𝒾
            -v
            ℓ ; RHS
            (-t.@ -h (Listof -t)))
;; Formula "head" is either a primitive operation or a stack address
(-h . ::= . -t ; TODO restrict
            ;; Hacky stuff
            -One-Of/C
            (-st/c.mk -𝒾)
            (-st/c.ac -𝒾 Index)
            (-->i.mk)
            (-->i.dom Index)
            (-->i.rng)
            (-->.mk)
            (-->*.mk)
            (-->.dom Index)
            (-->.rst)
            (-->.rng)
            (-ar.mk)
            (-ar.ctc)
            (-ar.fun)
            (-values.ac Index)
            (-≥/c Base)
            (-≤/c Base)
            (->/c Base)
            (-</c Base)
            (-≢/c Base)
            (-not/c -o)
            (-clo -⟦e⟧))
(-?t . ::= . -t #f)

(-special-bin-o . ::= . '> '< '>= '<= '= 'equal? 'eqv? 'eq? #|made up|# '≢)

;; convenient syntax
(define-match-expander -t.not
  (syntax-rules () [(_ t) (-t.@ 'not (list t))])
  (syntax-rules () [(_ t) (and t (-t.@ 'not (list t)))]))

(define-simple-macro (with-Γ+/- ([(Γ₁:id Γ₂:id) e])
                       #:true  e₁
                       #:false e₂)
  (let-values ([(Γ₁ Γ₂) e])
    (∪ (if Γ₁ e₁ ∅)
       (if Γ₂ e₂ ∅))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⌊ρ⌋ (Immutable-HashTable Symbol (Listof ℓ)))
(define-type -edge.tgt (U (Pairof -⟦e⟧ -⌊ρ⌋) -o -?t -h ℓ (-maybe-var ℓ) (Listof -edge.tgt) (℘ Base)))
(struct -edge ([tgt : -edge.tgt] [src : ℓ]) #:transparent)
(define-type -ℋ (Listof -edge))
(define-interner -H -ℋ
  #:intern-function-name -ℋ->-H
  #:unintern-function-name -H->-ℋ)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Some address values have `e` embeded in them.
;; This used to be a neccessary precision hack.
;; Nowaways it's just a temporary fix for the inaccurate source location returned
;; by `fake-contract`
(-α . ::= . ; For wrapped top-level definition
            (-α.wrp -𝒾)
            ; for binding
            (-α.x Symbol -H (℘ -h))
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
            (-α.fn [sym : (Option -⟦e⟧)] [mon-ctx : -ctx] [ctx : -H] [pc : -Γ])

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
            (-α.imm -V)
            ;; indirection for `listof` to keep in-sync with regular listof contracts
            (-α.imm-listof Symbol #|elem, ok with care|# -V ℓ)
            (-α.imm-ref-listof Symbol #|elem, ok with care|# -V ℓ)

            ;; Escaped fields
            (-α.escaped -𝒾 Integer)
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
(define-type -⟦e⟧ (-ρ -$ -Γ -H -Σ -⟦k⟧ → (℘ -ς)))
(define-type -⟦k⟧ (-A -$ -Γ -H -Σ     → (℘ -ς)))
(define-type -⟦f⟧ (ℓ (Listof -W¹) -$ -Γ -H -Σ -⟦k⟧ → (℘ -ς)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(struct -ς ([block : -αₖ]) #:transparent)
#|block start |# (struct -ς↑ -ς () #:transparent)
#|block return|# (struct -ς↓ -ς ([cache : -$] [pc : -Γ] [ans : -W]) #:transparent)
#|block raise |# (struct -ς! -ς ([blm : -blm]) #:transparent)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(struct -αₖ ([cache : -$]) #:transparent)
(struct -B -αₖ ([ctx : -H] [var : -formals] [exp : -⟦e⟧] [env : -ρ] [pc : -Γ]) #:transparent)
(struct -M -αₖ ([ctx : -H] [blm-ctx : -ctx] [ctc : -W¹] [val : -W¹] [pc : -Γ]) #:transparent) ; Contract monitoring
(struct -F -αₖ ([ctx : -H] [l : -l] [loc : ℓ] [ctc : -W¹] [val : -W¹] [pc : -Γ]) #:transparent) ; Flat checking
(struct -HV -αₖ ([tag : HV-Tag]) #:transparent) ; Havoc

(-αₖ:ctx . ::= . (-B:ctx -H -formals -⟦e⟧ -ρ)
                 (-M:ctx -H -ctx -W¹ -W¹)
                 (-F:ctx -H -l ℓ -W¹ -W¹)
                 (-HV:ctx HV-Tag))
(struct -αₖ:pth ([cache : -$] [pc : -Γ]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Verification Result
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-R . ::= . '✓ '✗ '?)

;; Take the first definite result
(define-syntax first-R
  (syntax-rules ()
    [(_) '?]
    [(_ R) R]
    [(_ R₁ R ...)
     (let ([ans R₁])
       (case ans
         ['? (first-R R ...)]
         [else ans]))]))

(: not-R : -R → -R)
;; Negate provability result
(define (not-R R)
  (case R [(✓) '✗] [(✗) '✓] [else '?]))

(: boolean->R : Boolean → (U '✓ '✗))
(define (boolean->R x) (if x '✓ '✗))


(define-signature env^
  ([⊥ρ : -ρ]
   [ρ@ : (-ρ Symbol → ⟪α⟫)]
   [ρ+ : (-ρ Symbol ⟪α⟫ → -ρ)]
   [-x-dummy : Symbol]))

(define-signature sto^
  ([⊥σ : -σ]
   [σ@ : ((U -Σ -σ) ⟪α⟫ → (℘ -V))]
   [σ@¹ : ((U -Σ -σ) ⟪α⟫ → -V)]
   [σ@/list : ((U -Σ -σ) (Listof ⟪α⟫) → (℘ (Listof -V)))]
   [defined-at? : ((U -Σ -σ) ⟪α⟫ → Boolean)]
   [σ-remove! : (-Σ ⟪α⟫ -V → Void)]
   [⊥σₖ : -σₖ]
   [σₖ@ : ((U -Σ -σₖ) -αₖ → (℘ -κ))]
   [⟪α⟫ₒₚ : ⟪α⟫]
   [⊤$ : -$]
   [⊤$* : -δ$]
   [$-set : (-$ -loc -?t → -$)]
   [$-set* : (-$ (Listof -loc) (Listof -?t) → -$)]
   [$-set! : (-Σ -$ ⟪α⟫ -loc -?t → -$)]
   [$-del : (-$ -loc → -$)]
   [$-del* : (-$ (Sequenceof -loc) → -$)]
   [$@! : (-Σ -Γ ⟪α⟫ -$ -loc ℓ → (Values (℘ -W¹) -$))]
   [$-extract : (-$ (Sequenceof -loc) → -δ$)]
   [$-restore : (-$ -δ$ → -$)]
   [$↓ : (-$ (℘ -loc) → -$)]
   [$-cleanup : (-$ → -$)]
   [$-symbolic-names : (-$ → (℘ (U Symbol ℓ)))]
   [⊥𝒜 : -𝒜]
   [get-aliases : (-Σ ⟪α⟫ → (℘ -loc))]
   [hack:α->loc : (⟪α⟫ → (Option -loc))]
   [mutable? : (⟪α⟫ → Boolean)]
   [escaped-field-addresses : (-σ → (℘ ⟪α⟫))]
   ))

(define-signature val^
  ([+● : (-h * → -●)]
   [+W¹ : ([-prim] [-?t] . ->* . -W¹)]
   [+W : ([(Listof -prim)] [-?t] . ->* . -W)]
   [W¹->W : (-W¹ → -W)]
   [W->W¹s : (-W -> (Listof -W¹))]
   [C-flat? : (-V → Boolean)]
   [with-negative-party : (-l -V → -V)]
   [with-positive-party : (-l -V → -V)]
   [behavioral? : (-σ -V → Boolean)]
   [guard-arity : (-=>_ → Arity)]
   [blm-arity : (ℓ -l Arity (Listof -V) → -blm)]
   [predicates-of-V : (-V → (℘ -h))]
   ))

(define-signature pc^
  ([⊤Γ : -Γ]
   [Γ↓ : (-Γ (℘ (U Symbol ℓ)) → -Γ)]
   [t-contains? : (-t -t → Boolean)]
   [t-contains-any? : (-t (℘ -t) → Boolean)]
   [bin-o->h : (-special-bin-o → Base → -h)]
   [flip-bin-o : (-special-bin-o → -special-bin-o)]
   [neg-bin-o : (-special-bin-o → -special-bin-o)]
   [complement? : (-t -t →  Boolean)]
   ;; simp
   [?t@ : ((Option -h) -?t * → -?t)]
   [op-≡? : (Any → Boolean)]
   ;; split
   [-struct/c-split : (-?t -𝒾 → (Listof -?t))]
   [-struct-split : (-?t -𝒾 → (Listof -?t))]
   [-ar-split : (-?t → (Values -?t -?t))]
   [-->-split : (-?t (U Index arity-at-least) → (Values (-maybe-var -?t) -?t))]
   [-->i-split : (-?t Index → (Values (Listof -?t) -?t))]
   [split-values : (-?t Natural → (Listof -?t))]
   ;; constr
   [-?list : ((Listof -?t) → -?t)]
   [-?unlist : (-?t Natural → (Listof -?t))]
   [-app-split : (-h -?t Natural → (Listof -?t))]
   [-?-> : ((-maybe-var -?t) -?t → -?t)]
   [-?->i : ((Listof -?t) (Option -λ) → -?t)]
   ;; path-cond
   [predicates-of : (-Γ -?t → (℘ -h))]
   [fvₜ : (-?t → (℘ (U Symbol ℓ)))]
   ))

(define-signature summ^
  ([⊥Ξ : -Ξ]
   [αₖ->ctx+pth : (-αₖ → (Values -αₖ:ctx -αₖ:pth))]
   [ctx+pth->αₖ : (-αₖ:ctx -αₖ:pth → -αₖ)]))

(define-signature instr^
  ([H∅ : -H]
   [H+ : (-H -edge → (Values -H Boolean))]
   [strip-C : (-V → -edge.tgt)]
   [⌊ρ⌋ : (-ρ → -⌊ρ⌋)]
   ))

(define-signature pretty-print^
  ([show-ς : (-ς → Sexp)]
   [show-σ : (-σ → (Listof Sexp))]
   [show-h : (-h → Sexp)]
   [show-t : (-?t → Sexp)]
   [show-Γ : (-Γ → (Listof Sexp))]
   [show-$ : (-$ → (Listof Sexp))]
   [show-δ$ : (-δ$ → (Listof Sexp))]
   [show-σₖ : (-σₖ → (Listof Sexp))]
   [show-blm-reason : ((U -V -v -h) → Sexp)]
   [show-V : (-V → Sexp)]
   [show-⟪α⟫ℓ : (-⟪α⟫ℓ → Symbol)]
   [show-⟪α⟫ℓs : ((Listof -⟪α⟫ℓ) → Sexp)]
   [show-A : (-A → Sexp)]
   [show-W¹ : (-W¹ → Sexp)]
   [show-⟦e⟧ : (-⟦e⟧ → Sexp)]
   [show-αₖ : (-αₖ → Sexp)]
   [show-edge : (-edge → Sexp)]
   [show-H : (-H → Sexp)]
   [show-⟪α⟫ : (⟪α⟫ → Sexp)]
   [show-κ : (-κ → Sexp)]
   [show-ρ : (-ρ → (Listof Sexp))]
   [show-loc : (-loc → Sexp)]
   [remember-e! : (-e -⟦e⟧ → -⟦e⟧)]
   [recall-e : (-⟦e⟧ → (Option -e))]
   [verbose? : (Parameterof Boolean)]
   ))
