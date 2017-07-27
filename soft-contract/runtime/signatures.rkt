#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         syntax/parse/define
         typed/racket/unit
         bnf
         intern
         set-extras
         "../ast/definition.rkt"
         )

(define-type -ρ (HashTable Symbol ⟪α⟫))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -σ (HashTable ⟪α⟫ (℘ -V)))
(define-type -σₖ (HashTable -αₖ (℘ -κ)))
(define-type -M (HashTable -αₖ (℘ -ΓA)))
(define-type -𝒜 (HashTable ⟪α⟫ (℘ -loc)))

;; Grouped mutable references to stores
(struct -Σ ([σ : -σ] [σₖ : -σₖ] [M : -M] [𝒜 : -𝒜]) #:mutable #:transparent)

(struct -κ ([cont : -⟦k⟧]    ; rest of computation waiting on answer
            [pc : -Γ]       ; path-condition to use for rest of computation
            [res : -?t]
            [to-restore : -$*]
            [to-invalid : (℘ -loc)]
            [looped? : Boolean])
  #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Runtime Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . -prim
            (-● (℘ -h))
            (-St -𝒾 (Listof ⟪α⟫))
            (-Vector (Listof ⟪α⟫))
            (-Vector^ [content : ⟪α⟫] [length : #|restricted|# -V])
            (-Hash^ [key : ⟪α⟫] [val : ⟪α⟫] [immutable? : Boolean])
            -Fn
            
            ;; Proxied higher-order values
            ;; Inlining the contract in the data definition is ok
            ;; because there's no recursion
            (-Ar [guard : -=>_] [v : ⟪α⟫] [ctx : -l³])
            (-St* [guard : -St/C] [val : ⟪α⟫] [ctx : -l³])
            (-Vector/guard [guard : (U -Vector/C -Vectorof)] [val : ⟪α⟫] [ctx : -l³])
            (-Hash/guard [guard : -Hash/C] [val : ⟪α⟫] [ctx : -l³])
            
            -C)

(-Fn . ::= . (-Clo -formals -⟦e⟧ -ρ -Γ)
             (-Case-Clo (Listof (Pairof (Listof Symbol) -⟦e⟧)) -ρ -Γ))

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
            (-Hash/C [key : -⟪α⟫ℓ] [val : -⟪α⟫ℓ]))

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (-maybe-var -⟪α⟫ℓ)] [rng : (U (Listof -⟪α⟫ℓ) 'any)] [pos : ℓ])
              (-=>i [doms : (Listof -⟪α⟫ℓ)]
                    [mk-rng : (List -Clo -λ ℓ)]
                    [pos : ℓ])
              (-Case-> (Listof (Pairof (Listof ⟪α⟫) ⟪α⟫)) [pos : ℓ]))

(struct -blm ([violator : -l]
              [origin : -l]
              [c : (Listof (U -V -v -h))]
              [v : (Listof -V)]
              [loc : ℓ]) #:transparent)
(struct -W¹ ([V : -V] [t : -?t]) #:transparent)
(struct -W ([Vs : (Listof -V)] [t : -?t]) #:transparent)
(-A . ::= . -W -blm)
(struct -ΓA ([cnd : -Γ] [ans : -A]) #:transparent)

(struct -⟪α⟫ℓ ([addr : ⟪α⟫] [loc : ℓ]) #:transparent)

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Symbols and Path Conditions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-loc . ::= . ;; references
              Symbol -𝒾
              ;; struct field or vector access with concrete offset
              (-loc.offset Index -t)
              )

(define-type -$ (HashTable -loc -W¹))
(define-type -$* (HashTable -loc (Option -W¹)))

;; Path condition is set of terms known to have evaluated to non-#f
;; It also maintains a "canonicalized" symbolic name for each variable
(define-type -Γ (℘ -t))

;; First order term for use in path-condition
(-t . ::= . -x
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
            (-≡/c Base)
            (-≢/c Base)
            (-not/c -o))
(-?t . ::= . -t #f)

(-special-bin-o . ::= . '> '< '>= '<= '= 'equal? 'eqv? 'eq? #|made up|# '≢)

(define-match-expander -not/c/simp
  (syntax-rules ()
    [(_ p) (-not/c p)])
  (syntax-rules ()
    [(_ p) (case p
             [(negative?) (-≥/c 0)]
             [(    zero?) (-≢/c 0)]
             [(positive?) (-≤/c 0)]
             [else (-not/c p)])]))

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

(define-type -edge.tgt (U -⟦e⟧ -o (Listof (U Symbol ℓ -⟦e⟧ -?t)) (℘ Base)))
(struct -edge ([tgt : -edge.tgt] [src : ℓ]) #:transparent)
(define-type -ℋ (Listof -edge))
(define-interner -⟪ℋ⟫ -ℋ
  #:intern-function-name -ℋ->-⟪ℋ⟫
  #:unintern-function-name -⟪ℋ⟫->-ℋ)


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
            (-α.x Symbol -⟪ℋ⟫)
            (-α.fv -⟪ℋ⟫)
            ; for struct field
            (-α.fld [id : -𝒾] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            ; for Cons/varargs
            ; idx prevents infinite list
            (-α.var-car [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : (Option Natural)])
            (-α.var-cdr [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : (Option Natural)])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [loc : ℓ] [ctx : -⟪ℋ⟫] [l+ : -l])

            ;; for vector indices
            (-α.idx [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            
            ;; for vector^ content
            (-α.vct [loc : ℓ] [ctx : -⟪ℋ⟫])

            ;; for hash^ content
            (-α.hash.key [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.hash.val [loc : ℓ] [ctx : -⟪ℋ⟫])

            ;; for wrapped vector
            (-α.unvct [loc : ℓ] [ctx : -⟪ℋ⟫] [l+ : -l])

            ;; for wrapped hash
            (-α.unhsh [loc : ℓ] [ctx : -⟪ℋ⟫] [l+ : -l])

            ;; for contract components
            (-α.and/c-l [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.and/c-r [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.or/c-l [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.or/c-r [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.not/c [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.vector/c [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.vectorof [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.hash/c-key [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.hash/c-val [val : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.struct/c [sym : -?t] [id : -𝒾] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.x/c Symbol)
            (-α.dom [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.rst [sym : -?t] [loc : ℓ] [ctd : -⟪ℋ⟫])
            (-α.rng [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.fn [sym : (U -?t -⟦e⟧)] [mon-loc : ℓ] [ctx : -⟪ℋ⟫] [l+ : -l] [pc : -Γ])

            ;; HACK
            (-α.hv)
            (-α.mon-x/c Symbol -⟪ℋ⟫ -l)
            (-α.fc-x/c Symbol -⟪ℋ⟫)
            (-α.fn.●)
            -o
            -𝒾
            )

(define-interner ⟪α⟫ -α
  #:intern-function-name -α->⟪α⟫
  #:unintern-function-name ⟪α⟫->-α)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A computation returns set of next states
;; and may perform side effects widening mutable store(s)
(define-type -⟦e⟧ (-ρ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))
(define-type -⟦k⟧ (-A -$ -Γ -⟪ℋ⟫ -Σ     → (℘ -ς)))
(define-type -⟦o⟧ (-⟪ℋ⟫ ℓ -Σ -$ -Γ (Listof -W¹) → (℘ -ΓA)))
(define-type -⟦f⟧ (ℓ (Listof -W¹) -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))
(-Prim . ::= . (-⟦o⟧.boxed -⟦o⟧) (-⟦f⟧.boxed -⟦f⟧))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(struct -ς ([block : -αₖ]) #:transparent)
#|block start |# (struct -ς↑ -ς () #:transparent)
#|block return|# (struct -ς↓ -ς ([cache : -$] [pc : -Γ] [ans : -A]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(struct -αₖ ([cache : -$] [ctx : -⟪ℋ⟫]) #:transparent)
(struct -ℬ -αₖ ([var : -formals] [exp : -⟦e⟧] [env : -ρ] [pc : -Γ]) #:transparent)
(struct -ℳ -αₖ ([l³ : -l³] [loc : ℓ] [ctc : -W¹] [val : -W¹] [pc : -Γ]) #:transparent) ; Contract monitoring
(struct -ℱ -αₖ ([l : -l] [loc : ℓ] [ctc : -W¹] [val : -W¹] [pc : -Γ]) #:transparent) ; Flat checking
(struct -ℋ𝒱 -αₖ () #:transparent) ; Havoc


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
   [⊥M : -M]
   [M@ : ((U -Σ -M) -αₖ → (℘ -ΓA))]
   [⟪α⟫ₕᵥ : ⟪α⟫]
   [⟪α⟫ₒₚ : ⟪α⟫]
   [⊤$ : -$]
   [⊤$* : -$*]
   [$-set : (-$ -loc -W¹ → -$)]
   [$-set* : (-$ (Listof -loc) (Listof -W¹) → -$)]
   [$-set! : (-Σ -$ ⟪α⟫ -loc -W¹ → -$)]
   [$-del : (-$ -loc → -$)]
   [$-del* : (-$ (Sequenceof -loc) → -$)]
   [$@! : (-Σ ⟪α⟫ -$ -loc → (℘ (Pairof -W¹ -$)))]
   [$-extract : (-$ (Sequenceof -loc) → -$*)]
   [$-restore : (-$ -$* → -$)]
   [$↓ : (-$ (℘ -loc) → -$)]
   [⊥𝒜 : -𝒜]
   [get-aliases : (-Σ ⟪α⟫ → (℘ -loc))]
   [hack:α->loc : (⟪α⟫ → (Option -loc))]
   ))

(define-signature val^
  ([+● : (-h * → -●)]
   [+W¹ : ([-prim] [-?t] . ->* . -W¹)]
   [+W : ([(Listof -prim)] [-?t] . ->* . -W)]
   [W¹->W : (-W¹ → -W)]
   [C-flat? : (-V → Boolean)]
   [with-negative-party : (-l -V → -V)]
   [with-positive-party : (-l -V → -V)]
   [approximate-under-contract : (-V → -V)]
   [behavioral? : (-σ -V → Boolean)]
   [guard-arity : (-=>_ → Arity)]
   [blm-arity : (ℓ -l Arity (Listof -V) → -blm)]
   [strip-C : (-V → -edge.tgt)]
   ))

(define-signature pc^
  ([⊤Γ : -Γ]
   [Γ↓ : (-Γ (℘ Symbol) → -Γ)]
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
   [fvₜ : (-?t → (℘ Symbol))]
   ))

(define-signature instr^
  ([⟪ℋ⟫∅ : -⟪ℋ⟫]
   [⟪ℋ⟫+ : (-⟪ℋ⟫ -edge → (Values -⟪ℋ⟫ Boolean))]
   ))

(define-signature pretty-print^
  ([show-ς : (-ς → Sexp)]
   [show-σ : (-σ → (Listof Sexp))]
   [show-M : (-M → (Listof Sexp))]
   [show-h : (-h → Sexp)]
   [show-t : (-?t → Sexp)]
   [show-Γ : (-Γ → (Listof Sexp))]
   [show-$ : (-$ → (Listof Sexp))]
   [show-σₖ : (-σₖ → (Listof Sexp))]
   [show-blm-reason : ((U -V -v -h) → Sexp)]
   [show-V : (-V → Sexp)]
   [show-⟪α⟫ℓ : (-⟪α⟫ℓ → Symbol)]
   [show-⟪α⟫ℓs : ((Listof -⟪α⟫ℓ) → Sexp)]
   [show-ΓA : (-ΓA → Sexp)]
   [show-A : (-A → Sexp)]
   [show-W¹ : (-W¹ → Sexp)]
   [show-⟦e⟧ : (-⟦e⟧ → Sexp)]
   [show-αₖ : (-αₖ → Sexp)]
   [show-edge : (-edge → Sexp)]
   [show-⟪ℋ⟫ : (-⟪ℋ⟫ → Sexp)]
   [show-⟪α⟫ : (⟪α⟫ → Sexp)]
   [show-ρ : (-ρ → (Listof Sexp))]
   [show-κ : (-κ → Sexp)]
   [show-loc : (-loc → Sexp)]
   [remember-e! : (-e -⟦e⟧ → -⟦e⟧)]
   [recall-e : (-⟦e⟧ → (Option -e))]
   [verbose? : (Parameterof Boolean)]
   ))
