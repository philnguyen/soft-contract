#lang typed/racket/base

(require typed/racket/unit
         racket/match
         racket/set
         set-extras
         "../utils/debug.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(provide instr@)

(define-unit instr@
  (import local-prover^ pretty-print^ widening^)
  (export instr^)

  (: ℋ+ : -ℋ -edge  → (Values -ℋ Boolean))
  ;; Add edge on top of call history.
  ;; If the target is already there, return the history chunk up to first time the target
  ;; is seen
  (define (ℋ+ ℋ x)

    (: match? : (-edge → Boolean))
    (define match?
      (match-let ([(-edge tgt src) x])
        (match-lambda
          [(-edge tgt* _) (and (not (symbol? tgt*)) (tgt=? tgt* tgt))])))

    (define ?ℋ (memf match? ℋ))
    (if ?ℋ (values ?ℋ #t) (values (cons x ℋ) #f)))
  
  (define ⟪ℋ⟫∅
    (let ([ℋ∅ : -ℋ '()])
      (-ℋ->-⟪ℋ⟫ ℋ∅)))

  (: ⟪ℋ⟫+ : -⟪ℋ⟫ -edge → (Values -⟪ℋ⟫ Boolean))
  (define (⟪ℋ⟫+ ⟪ℋ⟫ e)
    (define-values (ℋ* looped?) (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e))
    (values (-ℋ->-⟪ℋ⟫ ℋ*) looped?))

  (: ⌊ρ⌋ : -ρ → -⌊ρ⌋)
  (define (⌊ρ⌋ ρ)
    (for/hasheq : -⌊ρ⌋ ([(x α) ρ])
      (match (⟪α⟫->-α (cast α ⟪α⟫))
        [(-α.x x ⟪ℋ⟫ _) (values x (map -edge-src (-⟪ℋ⟫->-ℋ ⟪ℋ⟫)))])))

  (define ⌊ρ⌋₀ : -⌊ρ⌋ (hasheq))

  (: strip-C : -V → -edge.tgt)
  (define (strip-C C)
    (define get-ℓ : ((-maybe-var -⟪α⟫ℓ) → (-maybe-var ℓ))
      (match-lambda
        [(? list? l) (map -⟪α⟫ℓ-loc l)]
        [(-var l x) (-var (map -⟪α⟫ℓ-loc l) (-⟪α⟫ℓ-loc x))]))
    
    (match C
      [(-Clo xs ⟦e⟧ ρ _) (list 'flat (cons ⟦e⟧ (⌊ρ⌋ ρ)))]
      [(-And/C _ (-⟪α⟫ℓ _ ℓ₁) (-⟪α⟫ℓ _ ℓ₂)) (list 'and/c ℓ₁ ℓ₂)]
      [(-Or/C  _ (-⟪α⟫ℓ _ ℓ₁) (-⟪α⟫ℓ _ ℓ₂)) (list  'or/c ℓ₁ ℓ₂)]
      [(-Not/C (-⟪α⟫ℓ _ ℓ)) (list 'not/c ℓ)]
      [(-One-Of/C bs) bs]
      [(-St/C _ (-𝒾 𝒾 _) ⟪α⟫ℓs) (cons 𝒾 (map -⟪α⟫ℓ-loc ⟪α⟫ℓs))]
      [(-Vectorof (-⟪α⟫ℓ _ ℓ)) (list 'vectorof ℓ)]
      [(-Vector/C ⟪α⟫ℓs) (cons 'vector/c (map -⟪α⟫ℓ-loc ⟪α⟫ℓs))]
      [(-Hash/C (-⟪α⟫ℓ _ ℓₖ) (-⟪α⟫ℓ _ ℓᵥ)) (list 'hash/c ℓₖ ℓᵥ)]
      [(-Set/C (-⟪α⟫ℓ _ ℓ)) (list 'set/c ℓ)]
      [(-=> αs βs) (list '-> (get-ℓ αs) (if (list? βs) (get-ℓ βs) 'any))]
      [(-=>i αs (list _ _ ℓ)) (list '->i ℓ)]
      [(-Case-> cases) (list 'case-> (map strip-C cases))]
      [(-x/C α)
       (match-define (or (-α.x/c x _) (-α.imm-listof x _ _)) (⟪α⟫->-α α))
       (list 'recursive-contract/c x)]
      [(? -o? o) (list 'flat o)]
      [(-Ar _ (app ⟪α⟫->-α (-α.fn _ ctx _ _)) _) (list 'flat (-ctx-loc ctx))]
      [(-∀/C xs ⟦c⟧ ρ) (list '∀/c (cons ⟦c⟧ (⌊ρ⌋ ρ)))]
      [(-Seal/C x _ _) (list 'seal/c x)]
      [(and c (or (? ->/c?) (? -≥/c?) (? -</c?) (? -≤/c?) (? -≢/c?) (? -b?))) (list 'flat c)]
      [V (error 'strip-C "~a not expected" V)]))

  (: tgt=? : -edge.tgt -edge.tgt → Boolean)
  (define tgt=?
    (match-lambda**
     [((? list? l₁) (? list? l₂)) (and (equal? (length l₁) (length l₂)) (andmap tgt=? l₁ l₂))]
     [((cons ⟦e⟧₁ _) (cons ⟦e⟧₂ _)) (eq? ⟦e⟧₁ ⟦e⟧₂)]
     [(t₁ t₂) (equal? t₁ t₂)]))
  )
