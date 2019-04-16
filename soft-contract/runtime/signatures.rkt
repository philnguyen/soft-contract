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
                               (St α (℘ P))
                               (Vect α)
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
(#|Identities     |# T . ::= . γ (T:@ K (Listof (U T -b))))
(#|               |# K . ::= . γ '+ '- '* '/ 'equal? -st-ac)
(#|Environments   |# Γ .  ≜  . (Immutable-HashTable T S*))
(#|Stores         |# Ξ .  ≜  . (Immutable-HashTable α (Pairof S N)))
(#|Memories       |# Σ .  ≜  . (Pairof Ξ Γ))
(#|Env. Deltas    |# ΔΓ . ≜  . Γ)
(#|Store Deltas   |# ΔΞ . ≜  . Ξ)
(#|Memory Deltas  |# ΔΣ . ≜  . (Pairof ΔΞ ΔΓ))
(#|Stackabls      |# S* . ≜ . (U #|Values          |# V^
                                 #|Mutable Locations|# α))
(#|Storables      |# S .  ≜  . (U #|Stackables      |# S*
                                  #|Memory Blobs     |# (Vectorof V^)
                                  #|Closure Contexts |# Γ))
(#|Values Lists   |# W .  ≜  . (Listof V^))
(#|Non-Prim Funcs |# Fn . ::= . -λ ; delayed closure, for inlining
                                (Clo -formals E α)
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
                               (St/C α)
                               (Vectof/C α ℓ)
                               (Vect/C α)
                               (Hash/C α α ℓ)
                               (Set/C α ℓ))
(#|Func. Contracts|# Fn/C . ::= . (==>i [doms : (-var Dom)] [rng : (Option (Listof Dom))])
                                  (∀/C (Listof Symbol) E α)
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
(#|Pos. Predicates|# Q . ::= . -o (P:> (U T -b)) (P:≥ (U T -b)) (P:< (U T -b)) (P:≤ (U T -b)) (P:= (U T -b)) (P:arity-includes Arity) (P:≡ (U T -b)) (P:vec-len Index))
(#|Caches         |# $ .  ≜  . (Immutable-HashTable $:K R))
(#|Result         |# R .  ≜  . (Immutable-HashTable W (℘ ΔΣ)))
(#|Decisions      |# Dec . ::= . '✓ '✗)
(#|Maybe Decisions|# ?Dec . ≜ . (Option Dec))
(#|Addresses      |# α . ::= . γ (α:dyn β H))
(#|Static Addrs   |# γ . ::= . γ:ref
                               (γ:wrp -𝒾)
                               (γ:hv HV-Tag)
                               ;; Only use this in the prim DSL where all values are finite
                               ;; with purely syntactic components
                               γ:imm*
                               ;; Escaped struct field
                               (γ:escaped-field -𝒾 Index)) 
(#|Reference Addrs|# γ:ref . ::= . (γ:lex Symbol) (γ:top -𝒾))
(#|Immediate Addrs|# γ:imm* . ::= . (γ:imm #|restricted|# V)
                               (γ:imm:blob (Vectorof V^) ℓ)
                               (γ:imm:blob:st (Vectorof V^) ℓ -𝒾)
                               (γ:imm:listof     Symbol #|elem, ok with care|# V ℓ))
(#|Addr. Bases    |# β . ::= . ; closure's environment
                               (β:clo ℓ)
                               ; mutable cell
                               (β:mut (U Symbol -𝒾))
                               ; struct field
                               (β:st-elems (U ℓ Ctx (Pairof (U ℓ Symbol) (Option Index))) -𝒾)
                               ; for varargs
                               (β:var:car (U ℓ Symbol) (Option Natural))
                               (β:var:cdr (U ℓ Symbol) (Option Natural))
                               ;; for wrapped mutable struct
                               (β:st -𝒾 Ctx)
                               ;; for vector content blob
                               (β:vect-elems ℓ Index)
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
                               (β:vect/c-elems ℓ Index)
                               (β:vectof ℓ)
                               (β:hash/c:key ℓ)
                               (β:hash/c:val ℓ)
                               (β:set/c:elem ℓ)
                               (β:st/c-elems ℓ -𝒾)
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
(#|Cardinalities  |# N . ::= . 0 '? 1 'N)
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

(define-interner $:K $:Key
  #:intern-function-name intern-$:Key
  #:unintern-function-name unintern-$:Key)

(define ⊥R : R (hash))
(define H₀ : H ∅eq)
(define ⊥Ξ : Ξ (hash))
(define ⊥ΔΞ : ΔΞ ⊥Ξ)
(define ⊤Γ : Γ (hash))
(define ⊤ΔΓ : ΔΓ ⊤Γ)
(define ⊥Σ : Σ (cons ⊥Ξ ⊤Γ))
(define ⊥ΔΣ : ΔΣ ⊥Σ)
(define ⊥$ : $ (hasheq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Signatures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-signature sto^
  ([⧺ : (ΔΣ ΔΣ * → ΔΣ)]
   [Σ@ : (α Σ → V^)]
   [Σ@/raw : (α Σ → S)]
   [Σ@/blob : (α Σ → (Vectorof V^))]
   [Σ@/env : (α Σ → Γ)]
   [resolve : ((U Symbol -𝒾) Σ → V^)]
   [unpack : ((U V V^) Σ → V^)]; lookup with provings to eliminate spurious results
   [unpack-W : (W Σ → W)]
   [alloc : (α S → ΔΣ)]
   [alloc-top : (-𝒾 V^ → ΔΣ)]
   [alloc-top* : ((Listof -𝒾) W → ΔΣ)]
   [alloc-lex : (Σ Symbol V^ → ΔΣ)]
   [alloc-lex* : (Σ (Listof Symbol) W → ΔΣ)]
   [alloc-vararg : (Σ Symbol W → ΔΣ)]
   [alloc-rest : ([(U Symbol ℓ) W] [#:tail V^] . ->* . (Values V^ ΔΣ))]
   [mut : (α S Σ → ΔΣ)]
   [ΔΣ⊔ : (ΔΣ ΔΣ → ΔΣ)]
   [collapse-ΔΣs : ((℘ ΔΣ) → ΔΣ)]
   [ΔΣ⊔₁ : (ΔΣ (℘ ΔΣ) → (℘ ΔΣ))]
   [S-andmap : (∀ (X) (V^ → X) (α → X) S → (U X #t))]
   [S-ormap : (∀ (X) (V^ → X) (α → X) S → (U X #f))]
   [S-map : (∀ (X Y) (V^ → V^) S → S)]
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
   #;[V/ : (S → V → V)]
   [W⊔ : (W W → W)]
   [V⊔ : (V^ V^ → V^)]
   [V⊔₁ : (V V^ → V^)]
   [Ctx-with-site : (Ctx ℓ → Ctx)]
   [Ctx-with-origin : (Ctx ℓ → Ctx)]
   [Ctx-flip : (Ctx → Ctx)]
   [C-flat? : (V Σ → Boolean)]
   [C^-flat? : (V^ Σ → Boolean)]
   [arity : (V → (Option Arity))]
   [guard-arity : (Fn/C → Arity)]
   [with-negative-party : (-l V → V)]
   [with-positive-party : (-l V → V)]
   [ac-Ps : (-st-ac (℘ P) → (℘ P))]
   [merge/compact  : (∀ (X) (X X → (Option (Listof X))) X (℘ X) → (℘ X))]
   [merge/compact₁ : (∀ (X) (X X → (Option X)) X (℘ X) → (℘ X))]
   [Vect/C-fields : (Vect/C → (Values α ℓ Index))]
   [St/C-fields : (St/C → (Values α ℓ -𝒾))]
   [St/C-tag : (St/C → -𝒾)]
   [T-refers-to? : (T (℘ Symbol) → Boolean)]
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
   [show-S : (S → Sexp)]
   [show-V^ : (V^ → Sexp)]
   [show-W : (W → (Listof Sexp))]
   [show-Σ : (Σ → (Listof Sexp))]
   [show-Dom : (Dom → Sexp)]
   [show-R : (R → (Listof Sexp))]
   [show-Err : (Err → Sexp)]
   [show-$:Key : ($:Key → Sexp)]))
