#lang typed/racket/base

(provide prims-13@)

(require racket/match
         racket/set
         racket/contract
         typed/racket/unit
         "../ast/definition.rkt"
         "../runtime/signatures.rkt"
         "def-prim.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prims-13@
  (import prim-runtime^ proof-system^ widening^ app^ kont^ val^ pc^ sto^ instr^ env^)
  (export)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.1 Ports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; 13.1.2 Managing Ports
  (def-prim input-port? (any/c . -> . boolean?))
  (def-prim output-port? (any/c . -> . boolean?))
  (def-prim port? (any/c . -> . boolean?))
  (def-prim close-input-port (input-port? . -> . void?) #:lift-concrete? #f)
  (def-prim close-output-port (output-port? . -> . void?) #:lift-concrete? #f)
  (def-prim current-input-port  (-> input-port?) #:volatile? #t #:lift-concrete? #f)
  (def-prim current-output-port (-> output-port?) #:volatile? #t #:lift-concrete? #f)
  (def-prim current-error-port (-> output-port?) #:volatile? #t #:lift-concrete? #f)
  (def-const eof)
  (def-prim eof-object? (any/c . -> . boolean?))

  ;; 13.1.3 Port Buffers and Positions
  (def-prim flush-output (-> void?) #:lift-concrete? #f) ; FIXME uses

  ;; 13.1.5 File Ports
  ; [HO] call-with-input-file call-with-output-file
  (def-prim open-input-file (path-string? . -> . input-port?) #:volatile? #t #:lift-concrete? #f)
  (def-prim open-output-file (path-string? . -> . output-port?) #:volatile? #t #:lift-concrete? #f)

  (def-ext (call-with-input-file ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME uses
    #:domain ([W-p path-string?] [W-cb (input-port? . -> . any/c)])
    (define arg (-W¹ (-● {set 'input-port?}) (-x (+x!/memo 'cwif))))
    (app ℒ W-cb (list arg) Γ ⟪ℋ⟫ Σ ⟦k⟧))

  (def-ext (call-with-output-file ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧) ; FIXME uses
    #:domain ([W-p path-string?] [W-cb (output-port? . -> . any/c)])
    (define arg (-W¹ (-● {set 'output-port?}) (-x (+x!/memo 'cwof))))
    (app ℒ W-cb (list arg) Γ ⟪ℋ⟫ Σ ⟦k⟧))

  (def-ext with-input-from-file (path-string? (-> any/c) . -> . any/c))
  (def-ext with-output-to-file (path-string? (-> any/c) . -> . any/c))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.2 Byte and String Input
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-prim read-char (input-port? . -> . (or/c char? eof-object?)) #:volatile? #t #:lift-concrete? #f) ; FIXME uses
  (def-prim peek-char (input-port? . -> . (or/c char? eof-object?)) #:volatile? #t #:lift-concrete? #f) ; FIXME uses


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.3 Byte and String Output
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-prim write-char (char? output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
  (def-prim newline (output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.4 Reading
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (def-prim read (input-port? . -> . any/c) #:volatile? #t #:lift-concrete? #f) ; FIXME uses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 13.5 Writing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (def-prim write (any/c output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
  (def-prim display (any/c output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
  (def-prim displayln (any/c #;output-port? . -> . void?) #:lift-concrete? #f) ; FIXME uses
  (def-prim fprintf (->* (output-port? string?) #:rest list? void?) #:lift-concrete? #f)
  (def-prim printf (->* (string?) #:rest list? void?) #:lift-concrete? #f)
  (def-prim format ((string?) #:rest list? . ->* . string?))
  )

