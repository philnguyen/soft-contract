#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         typed/racket/unit
         bnf
         unreachable
         set-extras
         intern
         (only-in "../utils/list.rkt" NeListof)
         "../ast/signatures.rkt" 
         )

(E . ≜ . -e)

(#|Run-time Values|# V . ::= . -prim
                               (St -𝒾 (Listof α) (℘ P))
                               (Vect (Listof α))
                               (Vect-Of [content : α] [length : #|restricted|# V^])
                               (Empty-Hash)
                               (Hash-Of [key : α] [val : α])
                               (Empty-Set)
                               (Set-Of [elems : α])
                               Fn
                               (Guarded [ctx : (Pairof -l -l)] [guard : Prox/C] [val : α])
                               (Sealed α)
                               C
                               T
                               (-● (℘ P)))
(#|Identities     |# T . ::= . α (T:@ -o (Listof (U T -b))))
(#|Stores         |# Σ .  ≜  . (Immutable-HashTable α (Pairof V^ N)))
(#|Store Deltas   |# ΔΣ . ≜  . (Immutable-HashTable α (Pairof V^ N)))
(#|Values Lists   |# W .  ≜  . (Listof V^))
(#|Non-Prim Funcs |# Fn . ::= . (Clo -formals E (℘ α) ℓ)
                                (Case-Clo (Listof Clo) ℓ))
(#|Contracts      |# C . ::= . (And/C α α ℓ)
                               (Or/C α α ℓ)
                               (Not/C α ℓ)
                               (One-Of/C (℘ Base))
                               (X/C α)
                               Prox/C
                               (Seal/C α -l)
                               P)
(#|Proxies        |# Prox/C . ::= . Fn/C
                               (St/C -𝒾 (Listof α) ℓ)
                               (Vectof/C α ℓ)
                               (Vect/C (Listof α) ℓ)
                               (Hash/C α α ℓ)
                               (Set/C α ℓ))
(#|Func. Contracts|# Fn/C . ::= . (==>i [doms : (-var Dom)] [rng : (Option (Listof Dom))])
                                  (∀/C (Listof Symbol) E (℘ α) ℓ)
                                  (Case-=> (Listof ==>i))) 
(#|Errors         |# Err . ::= . (Err:Raised String ℓ)
                                 (Err:Undefined Symbol ℓ)
                                 (Err:Values Natural E W ℓ)
                                 (Err:Arity [proc : (U V ℓ)] [args : (U Natural W)] [site : ℓ])
                                 (Err:Varargs W V^ ℓ)
                                 (Err:Sealed [seal : Symbol] [site : ℓ])
                                 (Blm [violator : -l]
                                      [site : ℓ]
                                      [origin : ℓ]
                                      [ctc : W]
                                      [val : W]))
(#|Predicates     |# P . ::= . Q (P:¬ Q) (P:St (NeListof -st-ac) P))
(#|Pos. Predicates|# Q . ::= . -o (P:> (U T -b)) (P:≥ (U T -b)) (P:< (U T -b)) (P:≤ (U T -b)) (P:= (U T -b)) (P:arity-includes Arity) (P:≡ (U T -b)))
(#|Caches         |# $ .  ≜  . (Immutable-HashTable $:K (Pairof R (℘ Err))))
(#|Result         |# R .  ≜  . (Immutable-HashTable W ΔΣ))
(#|Decisions      |# Dec . ::= . '✓ '✗)
(#|Maybe Decisions|# ?Dec . ≜ . (Option Dec))
(#|Call Edge      |# K .  ≜  . (Pairof ℓ ℓ))
(#|Addresses      |# α . ::= . γ (α:dyn β H))
(#|Static Addrs   |# γ . ::= . (γ:lex Symbol)
                               (γ:top -𝒾)
                               (γ:wrp -𝒾)
                               (γ:hv HV-Tag)
                               ;; Only use this in the prim DSL where all values are finite
                               ;; with purely syntactic components
                               γ:imm*
                               ;; Escaped struct field
                               (γ:escaped-field -𝒾 Index)) 
(#|Immediate Addrs|# γ:imm* . ::= . (γ:imm #|restricted|# V)
                               ;; indirection for `listof` to keep in-sync with regular listof contracts
                               (γ:imm:listof     Symbol #|elem, ok with care|# V ℓ)
                               (γ:imm:ref-listof Symbol #|elem, ok with care|# V ℓ))
(#|Addr. Bases    |# β . ::= . ; escaped parameter
                               Symbol
                               ; mutable cell
                               (β:mut (U Symbol -𝒾))
                               ; struct field
                               (β:fld -𝒾 ℓ Natural)
                               ; wrapped struct field from monitoring
                               (β:fld/wrap -𝒾 Ctx Natural)
                               ; for varargs
                               (β:var:car (U ℓ Symbol) (Option Natural))
                               (β:var:cdr (U ℓ Symbol) (Option Natural))
                               ;; for wrapped mutable struct
                               (β:st -𝒾 Ctx)
                               ;; for vector indices
                               (β:idx ℓ Natural)
                               ;; for vect-of content
                               (β:vct ℓ)
                               ;; for hash-of content
                               (β:hash:key ℓ)
                               (β:hash:val ℓ)
                               ;; for set-of content
                               (β:set:elem ℓ)
                               ;; for wrapped vector
                               (β:unvct Ctx)
                               ;; for wrapped hash
                               (β:unhsh Ctx ℓ)
                               ;; for wrapped set
                               (β:unset Ctx ℓ)
                               ;; for contract components
                               (β:and/c:l ℓ)
                               (β:and/c:r ℓ)
                               (β:or/c:l ℓ)
                               (β:or/c:r ℓ)
                               (β:not/c ℓ)
                               (β:x/c Symbol)
                               (β:vect/c ℓ Natural)
                               (β:vectof ℓ)
                               (β:hash/c:key ℓ)
                               (β:hash/c:val ℓ)
                               (β:set/c:elem ℓ)
                               (β:st/c -𝒾 ℓ Natural)
                               (β:dom ℓ)
                               ;; for wrapped function
                               (β:fn Ctx Fn/C-Sig)
                               ;; For values wrapped in seals
                               (β:sealed Symbol ℓ) ; points to wrapped objects
                               )
(#|Cache Keys     |# $:Key . ::= . ($:Key:Exp Σ E)
                                   ($:Key:Mon Σ Ctx V V^)
                                   ($:Key:Fc Σ ℓ V V^)
                                   ($:Key:App Σ ℓ V W)
                                   ($:Key:Hv Σ α))
(#|Named Domains  |# Dom . ::= . (Dom [name : Symbol] [ctc : (U Clo α)] [loc : ℓ]))
(#|Cardinalities  |# N . ::= . 0 1 'N)
(#|Havoc Tags     |# HV-Tag . ≜ . (Option -l))
(#|Mon. Contexts  |# Ctx . ::= . (Ctx [pos : -l] [neg : -l] [origin : ℓ] [site : ℓ]))
(#|Cache Tags     |# $:Tag . ::= . 'app 'mon 'flc)
(#|Abstract Values|# V^ . ≜ . (℘ V))
(#|Abs. Val. Lists|# W^ . ≜ . (℘ W))
(#|Dynamic Context|# H  . ≜ . (℘ ℓ))
(#|Function Contract Signature|# Fn/C-Sig . ::= . [#:reuse (Pairof -formals (Option (Listof Symbol)))]
                                                  [#:reuse (Listof Fn/C-Sig)])

;; Size-change Stuff
(#|Size-change Graphs|# SCG . ≜ . (Immutable-HashTable (Pairof Integer Integer) Ch))
(#|Changes           |# Ch . ::= . '↓ '↧)

(#|Addr. Substitutions|# S . ≜ . (HashTable α α))
(Renamings . ≜ . (Immutable-HashTable α (Option T)))

(define-interner $:K $:Key
  #:intern-function-name intern-$:Key
  #:unintern-function-name unintern-$:Key)

;; Convenient patterns
(define-syntax-rule (define-St-matcher (P α ...) St-id)
  (define-match-expander P
    (syntax-rules () [(_ α ...) (St (== St-id) (list α ...) _)])
    (syntax-rules () [(_ α ...) (St St-id (list α ...) ∅)])))
(define-syntax-rule (define-St/G-matcher P St-id)
  (define-match-expander P
    (syntax-rules () [(_ α) (Guarded _ (St/C (== St-id) _ _) α)])))
(define-St-matcher (Cons αₕ αₜ) -𝒾-cons)
(define-St/G-matcher Guarded-Cons -𝒾-cons)
(define-St-matcher (Box α) -𝒾-box)
(define-St/G-matcher Guarded-Box -𝒾-box)

(define ⊥R : R (hash))
(define H₀ : H ∅eq)
(define ⊥Σ : Σ (hash))
(define ⊥ΔΣ : ΔΣ (hash))
(define ⊥$ : $ (hasheq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Signatures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-signature sto^
  ([⧺ : (ΔΣ ΔΣ * → ΔΣ)]
   [lookup : (α Σ → V^)]
   [Σ@ : (α Σ → V^)]
   [V@ : (Σ -st-ac V → V^)]
   [unpack : ((U V V^) Σ → V^)]; lookup with provings to eliminate spurious results
   [unpack-W : (W Σ → W)]
   [alloc : (α V^ → ΔΣ)]
   [alloc-lex : ((U Symbol -𝒾) V^ → ΔΣ)]
   [alloc-lex* : ((Listof (U Symbol -𝒾)) W → ΔΣ)]
   [alloc-vararg : (Symbol W → ΔΣ)]
   [alloc-rest : ([(U Symbol ℓ) W] [#:tail V^] . ->* . (Values V^ ΔΣ))]
   [alloc-each : (W (Natural → β) → (Values (Listof α) ΔΣ))]
   [resolve-lex : ((U Symbol -𝒾) → α)]
   [mut : (α V^ → ΔΣ)]
   [ΔΣ⊔ : (ΔΣ ΔΣ → ΔΣ)]
   [escape : ((℘ Symbol) Σ → (Values (℘ α) ΔΣ))]
   [stack-copy : ((℘ α) Σ → ΔΣ)]
   [ambiguous? : (T Σ → Boolean)]
   ))

(define-signature cache^
  ([R-of : ([(U V V^ W)] [ΔΣ] . ->* . R)]
   [ΔΣ⧺R : (ΔΣ R → R)]
   [R⧺ΔΣ : (R ΔΣ → R)]
   [collapse-R : (R → (Option (Pairof W^ ΔΣ)))]
   [collapse-R/ΔΣ : (R → (Option ΔΣ))]
   [R⊔ : (R R → R)]))

(define-signature val^
  ([collapse-W^ : (W^ → W)]
   [collapse-W^-by-arities : (W^ → (Immutable-HashTable Natural W))] 
   [V/ : (S → V → V)]
   [W⊔ : (W W → W)]
   [V⊔ : (V^ V^ → V^)]
   [V⊔₁ : (V V^ → V^)]
   [blur : (case->
            [V → V]
            [V^ → V^])]
   [Ctx-with-site : (Ctx ℓ → Ctx)]
   [Ctx-with-origin : (Ctx ℓ → Ctx)]
   [Ctx-flip : (Ctx → Ctx)]
   [C-flat? : (V Σ → Boolean)]
   [C^-flat? : (V^ Σ → Boolean)]
   [arity : (V → (Option Arity))]
   [guard-arity : (Fn/C → Arity)]
   [with-negative-party : (-l V → V)]
   [with-positive-party : (-l V → V)]
   [make-renamings : ((U (Listof Symbol) -formals) W → Renamings)]
   [rename : (Renamings → (case->
                           [T → (Option T)]
                           [(U T -b) → (Option (U T -b))]))]
   [T-root : (T:@ → (℘ α))]
   [ac-Ps : (-st-ac (℘ P) → (℘ P))]
   [merge/compact : (∀ (X) (X X → (Option (Listof X))) X (℘ X) → (℘ X))]
   ))

(define-signature prover^
  ([sat : (Σ V V^ → ?Dec)]
   [P⊢P : (Σ V V → ?Dec)]
   [refine-Ps : ((℘ P) V Σ → (℘ P))]
   [maybe=? : (Σ Integer V^ → Boolean)]
   [check-plaus : (Σ V W → (Values (Option (Pairof W ΔΣ)) (Option (Pairof W ΔΣ))))]
   [refine : (V^ (U V (℘ P)) Σ → (Values V^ ΔΣ))]
   [refine-not : (V^ V Σ → (Values V^ ΔΣ))]
   [reify : ((℘ P) → V^)]
   ))

(define-signature pretty-print^
  ([show-α : (α → Sexp)]
   [show-V : (V → Sexp)]
   [show-V^ : (V^ → Sexp)]
   [show-W : (W → (Listof Sexp))]
   [show-Σ : (Σ → (Listof Sexp))]
   [show-Dom : (Dom → Sexp)]
   [show-R : (R → (Listof Sexp))]
   [show-Err : (Err → Sexp)]
   [show-$:Key : ($:Key → Sexp)]))
