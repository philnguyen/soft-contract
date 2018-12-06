#lang typed/racket/base

(provide prims-scv@)

(require racket/match
         racket/contract
         typed/racket/unit
         set-extras
         "../utils/debug.rkt"
         "../utils/list.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-scv@
  (import prim-runtime^
          val^ pc^
          widening^)
  (export)

  (def (scv:make-case-lambda ℓ Ws $ Γ H Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)]
    (define-values (cases ts) (unzip-by -W¹-V -W¹-t Ws))
    (define t (-t.@ 'case-lambda (cast ts (Listof -t))))
    (⟦k⟧ (-W (list (-Case-Clo (cast cases (Listof -Clo)))) t) $ Γ H Σ))

  (def (scv:make-case-> ℓ Ws $ Γ H Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)]
    (define-values (cases ts) (unzip-by -W¹-V -W¹-t Ws))
    (define t (-t.@ 'case-> (cast ts (Listof -t))))
    (⟦k⟧ (-W (list (-Case-> (cast cases (Listof -=>)))) t) $ Γ H Σ))

  (def (scv:struct/c ℓ _ $ Γ H Σ ⟦k⟧)
    #:init ([Wₖ any/c])
    #:rest [Wᵣs (listof contract?)]
    (match Wₖ
      [(-W¹ (-st-mk 𝒾) _)
       (define-values (Cs cs) (unzip-by -W¹-V -W¹-t Wᵣs))
       (define αs ((inst build-list ⟪α⟫) (length Wᵣs) (λ (i) (-α->⟪α⟫ (-α.struct/c 𝒾 ℓ H i)))))
       (for ([α (in-list αs)] [C (in-list Cs)])
         (σ⊕V! Σ α C))
       (define αℓs : (Listof -⟪α⟫ℓ)
         (for/list ([α : ⟪α⟫ (in-list αs)] [i : Natural (in-naturals)])
           (-⟪α⟫ℓ α (ℓ-with-id ℓ i))))
       (define Wₐ (-W (list (-St/C (andmap C-flat? Cs) 𝒾 αℓs)) (apply ?t@ (-st/c.mk 𝒾) cs)))
       (⟦k⟧ Wₐ $ Γ H Σ)]
      [(-W¹ V _)
       (⟦k⟧ (blm/simp (ℓ-src ℓ) 'scv:struct/c '(constructor?) (list V) ℓ) $ Γ H Σ)]))
  
  )
