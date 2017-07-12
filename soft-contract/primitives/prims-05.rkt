#lang typed/racket/base

(provide prims-05@)

(require racket/contract
         racket/set
         typed/racket/unit
         "../runtime/signatures.rkt"
         "def-prim.rkt"
         "signatures.rkt")

(define-unit prims-05@
  (import prim-runtime^ val^ pc^ sto^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.3 Structure Type Properties
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-prim/custom (make-struct-type-property ⟪ℋ⟫ ℓ Σ $ Γ Ws)
    (define tₐ (apply ?t@ 'make-struct-type-property (map -W¹-t Ws)))
    (define ans
      (-W (list (-● {set 'struct-type-property?})
                (-● {set 'procedure?})
                (-● {set 'procedure?}))
          tₐ))
    {set (-ΓA Γ ans)})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.6 Structure Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-pred struct-type?))
