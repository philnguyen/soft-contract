#lang typed/racket/base

(provide prims-10@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         "../utils/list.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "def.rkt")

(define-unit prims-10@
  (import prim-runtime^ pc^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.1 Multiple Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def (values ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ()
    #:rest (Ws (listof any/c))
    (define-values (Vs ss) (unzip-by -W¹-V -W¹-t Ws))
    (⟦k⟧ (-W Vs (apply ?t@ 'values ss)) $ Γ ⟪ℋ⟫ Σ))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.2 Exception
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def raise (case->
              [any/c . -> . none/c]
              [any/c any/c . -> . none/c]))

  (def* (error raise-user-error raise-argument-error raise-arguments-error raise-result-error)
    (() #:rest list . ->* . none/c))

  (def-pred exn?)
  (def-pred exn:fail?)

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.4 Continuations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (def* (call-with-current-continuation call-with-escape-continuation)
    ; FIXME uses
    (∀/c (α) (((α . -> . none/c) . -> . α) . -> . α))
    #;(∀/c (α β)
         (case-> ; not first-orderly distinguishable
          [((-> none/c) . -> . (values)) . -> . (values)]
          [((α . -> . none/c) . -> . α) . -> . α]
          [((α β . -> . none/c) . -> . (values α β)) . -> . (values α β)]))) 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.5 Continuation Marks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def continuation-mark-set-first (() #:rest list? . ->* . any/c)) ; FIXME


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.7 Exiting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def exit
    (case->
     (-> none/c)
     (any/c . -> . none/c)))

  )
