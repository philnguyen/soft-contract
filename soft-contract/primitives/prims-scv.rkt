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
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(define-unit prims-scv@
  (import prim-runtime^)
  (export)

  (def (scv:make-case-lambda ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)]
    (define-values (cases ts) (unzip-by -W¹-V -W¹-t Ws))
    (define t (-t.@ 'case-lambda (cast ts (Listof -t))))
    (⟦k⟧ (-W (list (-Case-Clo (cast cases (Listof -Clo)))) t) $ Γ ⟪ℋ⟫ Σ))

  (def (scv:make-case-> ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)]
    (define-values (cases ts) (unzip-by -W¹-V -W¹-t Ws))
    (define t (-t.@ 'case-> (cast ts (Listof -t))))
    (⟦k⟧ (-W (list (-Case-> (cast cases (Listof -=>)))) t) $ Γ ⟪ℋ⟫ Σ)))
