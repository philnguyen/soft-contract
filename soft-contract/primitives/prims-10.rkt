#lang typed/racket/base

(provide prims-10@)

(require racket/contract
         racket/set
         typed/racket/unit
         "../utils/list.rkt"
         "../runtime/definition.rkt"
         "../runtime/simp.rkt"
         "def-prim.rkt"
         "signatures.rkt")

(define-unit prims-10@
  (import prim-runtime^)
  (export)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.1 Multiple Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-prim/custom (values ⟪ℋ⟫ ℒ Σ Γ Ws)
    (define-values (Vs ss) (unzip-by -W¹-V -W¹-t Ws))
    {set (-ΓA (-Γ-facts Γ) (-W Vs (apply ?t@ 'values ss)))})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.2 Exceptions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-prim/custom (error ⟪ℋ⟫ ℒ Σ Γ Ws)
    ;; Consider a user-written error to be a blame on some party other than the module itself
    {set (-ΓA (-Γ-facts Γ) (-blm 'exception 'error '(error) (map -W¹-V Ws) (-ℒ-app ℒ)))})


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.4 Continuations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-prim/todo call-with-current-continuation ((any/c . -> . any/c) . -> . any/c)) ; FIXME
  )

