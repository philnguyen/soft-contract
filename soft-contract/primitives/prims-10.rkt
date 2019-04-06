#lang typed/racket/base

(provide prims-10@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         "../utils/list.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
         "signatures.rkt"
         "def.rkt")

(define-unit prims-10@
  (import cache^
          prim-runtime^
          exec^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 10.1 Multiple Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def (values Σ ℓ W)
    #:init ()
    #:rest [W (listof any/c)]
    (R-of W))
  

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

  (def-struct srcloc ([source any/c]
                      [line (or/c #f exact-positive-integer?)]
                      [column (or/c #f exact-nonnegative-integer?)]
                      [position (or/c #f exact-positive-integer?)]
                      [span (or/c #f exact-nonnegative-integer?)])
    #:extra-constructor-name make-srcloc)

  
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
