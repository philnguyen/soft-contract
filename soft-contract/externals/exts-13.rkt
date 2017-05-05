#lang typed/racket/base

(provide exts-13@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/contract
         set-extras
         "../ast/definition.rkt"
         "../reduction/signatures.rkt"
         "../runtime/main.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-ext.rkt")

(define-unit exts-13@
  (import ext-runtime^ prim-runtime^ proof-system^ widening^ app^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.1 Ports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-ext (call-with-input-file $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME uses
    #:domain ([W-p path-string?] [W-cb (input-port? . -> . any/c)])
    (define arg (-W¹ (-● {set 'input-port?}) (-x (+x!/memo 'cwif))))
    (app $ ℒ W-cb (list arg) Γ ⟪ℋ⟫ Σ ⟦k⟧))

  (def-ext (call-with-output-file $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME uses
    #:domain ([W-p path-string?] [W-cb (output-port? . -> . any/c)])
    (define arg (-W¹ (-● {set 'output-port?}) (-x (+x!/memo 'cwof))))
    (app $ ℒ W-cb (list arg) Γ ⟪ℋ⟫ Σ ⟦k⟧))
  )
