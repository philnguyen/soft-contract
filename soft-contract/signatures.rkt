#lang typed/racket/base

(provide verifier^ reduction^ parser^ prims^ proof-system^ widening^ for-gc^ lib^ debugging^)

(require typed/racket/unit
         set-extras
         "ast/signatures.rkt"
         "runtime/signatures.rkt")

(define-signature verifier^
  ([run-files : ((Listof Path-String) → (Values (℘ -A) -Σ))]
   [havoc-files : ((Listof Path-String) → (Values (℘ -A) -Σ))]
   [havoc-files/profile : ([(Listof Path-String)] [#:delay Positive-Real] . ->* . (Values (℘ -A) -Σ))]
   [havoc-last-file : ((Listof Path-String) → (Values (℘ -A) -Σ))]
   [run-e : (-e → (Values (℘ -A) -Σ))]
   [debug-iter? : (Parameterof Boolean)]
   [debug-trace? : (Parameterof Boolean)]
   [max-steps : (Parameterof (Option Natural))]))

(define-signature lib^
  ([verify : (Syntax (HashTable Symbol Syntax) → Any)]))

(define-signature reduction^
  ([run : (-⟦e⟧ → (Values (℘ -A) -Σ))]))

(define-signature parser^ ; TODO
  ([parse-files : ((Listof Path-String) → (Listof -module))]
   [parse-module : (Syntax → -module)]
   [parse-expr : (Syntax → -e)]
   [canonicalize-path : (Path-String → Path-String)]))

(define-signature prims^ ; TODO
  ([get-prim : (Symbol → -⟦f⟧)]
   [o⇒o : (Symbol Symbol → -R)]
   [get-conservative-range : (Symbol → Symbol)]
   [get-exclusions : (Symbol → (℘ Symbol))]
   [prim-arity : (Symbol → Arity)]
   [parse-prim : (Identifier → (Option -prim))]
   [implement-predicate : (-σ -φ -o (Listof -V^) → -V^)]))

(define-signature proof-system^
  ([p⇒p : (-h -h → -R)]
   [V∈C : (-σ -φ -V^ (U -h -V) → -R)]
   [φ+/-pV^ : (-σ -φ -h -V^ * → (Values (℘ -φ) (℘ -φ)))]
   [p∋V^ : (-σ -φ -h -V^ * → -R)]
   [quick-p∋V^ : (-σ -φ -h -V^ * → -R)]
   [V+ : (-σ -φ -V^ (U -h -V) → -V^)]
   [V- : (-σ -φ -V^ (U -h -V) → -V^)]
   [φ+pV : (-φ -h (Listof -V) → -φ)]
   [plausible-index? : (-σ -φ -V^ Natural → Boolean)]
   [sat-one-of : (-V^ (℘ Base) → -R)]
   [V-arity : (case->
               [-Clo → Arity]
               [-Case-Clo → Arity]
               [-V → (Option Arity)])]))

;; FIXME: least coherent signature ever.
;; Could have named it "misc"...
(define-signature widening^
  ([V⊕ : (-φ -V^ -V^ → -V^)]
   [σ⊕ : (-σ -σ → -σ)]
   [compat? : (-φ -V -V → (Option (℘ -h)))]))

(define-signature for-gc^
  ([add-⟦k⟧-roots! : (-⟦k⟧ (℘ ⟪α⟫) → Void)]
   [⟦k⟧->roots : (-⟦k⟧ → (℘ ⟪α⟫))]
   [set-⟦k⟧->αₖ! : (-⟦k⟧ -αₖ → Void)]
   [⟦k⟧->αₖ : (-⟦k⟧ → -αₖ)]
   [V->⟪α⟫s : (-V → (℘ ⟪α⟫))]
   [ρ->⟪α⟫s : (-ρ → (℘ ⟪α⟫))]
   [αₖ->⟪α⟫s : (-αₖ -σₖ → (℘ ⟪α⟫))]
   [⟦k⟧->⟪α⟫s : (-⟦k⟧ -σₖ → (℘ ⟪α⟫))]
   [->⟪α⟫s : ((Rec X (U -⟪α⟫ℓ -V -ρ (Listof X) (℘ X) (Boxof ⟪α⟫))) → (℘ ⟪α⟫))]
   [σ-equal?/spanning-root : (-σ -σ (℘ ⟪α⟫) → Boolean)]
   [gc-αₖ : (-Σ -αₖ -⟦k⟧ → -αₖ)]
   [span-δσ : (-Σ -δσ (℘ ⟪α⟫) → -σ)]))

(define-signature debugging^
  ())
