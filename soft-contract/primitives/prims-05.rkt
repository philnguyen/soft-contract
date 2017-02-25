#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         racket/set
         "../runtime/main.rkt"
         "def-prim.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.3 Structure Type Properties
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-prim/custom (make-struct-type-property ⟪ℋ⟫ ℓ Σ Γ Ws)
  (define sₐ (apply -?@ 'make-struct-type-property (map -W¹-s Ws)))
  (define ans
    (-W (list (-● {set 'struct-type-property?})
              (-● {set 'procedure?})
              (-● {set 'procedure?}))
        sₐ))
  {set (-ΓA Γ ans)})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 5.6 Structure Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-pred struct-type?)
