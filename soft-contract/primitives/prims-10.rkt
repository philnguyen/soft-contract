#lang typed/racket/base

(provide (all-defined-out))

(require racket/contract
         racket/set
         "../../utils/list.rkt"
         "../../runtime/definition.rkt"
         "../../runtime/simp.rkt"
         "def-prim.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.1 Multiple Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim/custom (values ⟪ℋ⟫ ℓ l Σ Γ Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  {set (-ΓA Γ (-W Vs (apply -?@ 'values ss)))})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.4 Continuations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def-prim/todo call-with-current-continuation ((any/c . -> . any/c) . -> . any/c)) ; FIXME

