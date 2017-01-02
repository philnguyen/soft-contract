#lang typed/racket/base

(require racket/match
         racket/set
         racket/contract
         "../utils/set.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "../reduction/compile/app.rkt"
         "def-ext.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.1 Ports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ext (call-with-input-file l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME uses
  #:domain ([W-p path-string?] [W-cb (input-port? . -> . any/c)])
  (define arg (-W¹ (-● {set 'input-port?}) (-x (+x!/memo 'cwif))))
  (app l $ ℒ W-cb (list arg) Γ ⟪ℋ⟫ Σ ⟦k⟧))

(def-ext (call-with-output-file l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME uses
  #:domain ([W-p path-string?] [W-cb (output-port? . -> . any/c)])
  (define arg (-W¹ (-● {set 'output-port?}) (-x (+x!/memo 'cwof))))
  (app l $ ℒ W-cb (list arg) Γ ⟪ℋ⟫ Σ ⟦k⟧))
