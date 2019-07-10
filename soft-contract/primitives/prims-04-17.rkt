#lang typed/racket/base

(require racket/match
         racket/contract
         racket/bool
         racket/string
         racket/math
         racket/list
         racket/stream
         racket/dict
         racket/function
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/flonum
         racket/fixnum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         unreachable
         "../utils/debug.rkt"
         "../utils/pretty.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-17@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.17 Procedures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-17@
  (import val^ cache^ sto^
          prim-runtime^ prover^
          exec^ app^)
  (export)

  (def-pred procedure?)
  (define ℓ:apply (loc->ℓ (loc 'apply 0 0 '())))
  (def (apply Σ ℓ args)
    #:init ()
    #:rest [args (listof any/c)] ; manual arity check instead
    (define n (length args))
    ;; Instead of pattern matching to get around TR cast
    (if (>= n 2)
        (match-let-values ([(Vₕ) (car args)]
                           [(Wₓ (list Vᵣ)) (split-at (cdr args) (- n 2))])
          (app/rest Σ ℓ Vₕ Wₓ Vᵣ))
        (begin (err! (Err:Arity 'apply args ℓ))
               ⊥R)))
  
  (def compose ; FIXME uses
    (∀/c (α β γ)
         (case->
          [(β . -> . γ) (α . -> . β) . -> . (α . -> . γ)])))
  (def compose1 ; FIXME uses
    (∀/c (α β γ)
         (case->
          [(β . -> . γ) (α . -> . β) . -> . (α . -> . β)])))
  (def procedure-rename (∀/c (α) ((and/c procedure? α) symbol? . -> . α)))
  (def procedure->method (∀/c (α) ((and/c procedure? α) . -> . α)))
  (def-pred procedure-closure-contents-eq? (procedure? procedure?))

  ;; 4.17.1 Keywords and Arity
  ;[keyword-apply #|FIXME uses|#]
  (def (procedure-arity Σ ℓ W)
    #:init ([Vₕ procedure?])
    (R-of (for/set : V^ ([V (in-set (unpack Vₕ Σ))])
            (cond [(arity V) => -b] [else (-● ∅)]))))
  (def-pred procedure-arity?)
  {def-pred procedure-arity-includes? (procedure? exact-nonnegative-integer?)} ; FIXME uses
  (def procedure-reduce-arity
    (procedure? procedure-arity? . -> . procedure?))
  (def procedure-keywords ; FIXME
     (procedure? . -> . (values (listof keyword?) (or/c (listof keyword?) not))))
  #;[make-keyword-procedure ; FIXME uses
     ((((listof keyword?) list?) () #:rest list? . ->* . any) . -> . procedure?)]
  #;[procedure-reduce-keyword-arity ; FIXME
     (procedure? procedure-arity? (listof keyword?) (or/c (listof keyword?) not)
                 . -> . procedure?)]
  (def-pred arity-at-least?)
  (def arity-at-least (exact-nonnegative-integer? . -> . arity-at-least?))
  (def arity-at-least-value (arity-at-least? . -> . exact-nonnegative-integer?))
  (def-alias make-arity-at-least arity-at-least)
  (def-opq prop:procedure struct-type-property?)
  [def-pred procedure-struct-type? (struct-type?)]
  (def procedure-extract-target (procedure? . -> . (or/c procedure? not)))
  (def-opq prop:arity-string struct-type-property?)
  (def-opq prop:checked-procedure struct-type-property?)
  (def checked-procedure-check-and-extract
    (∀/c (_) (struct-type? _ (any/c any/c any/c . -> . _) _ _ . -> . any/c)))

  ;; 4.17.2 Reflecting on Primitives
  (def-pred primitive?)
  (def-pred primitive-closure?)
  (def primitive-result-arity (primitive? . -> . procedure-arity?))

  ;; 4.17.3 Additional Higher-Order Functions
  (def identity (∀/c (α) (α . -> . α)))
  (def const (∀/c (α) (α . -> . (() #:rest list? . ->* . α))))
  (def negate (procedure? . -> . procedure?))
  ;[curry ] FIXME
  ;[curryr] FIXME
  (def-pred normalized-arity?)
  (def normalize-arity ; FIXME dependency
    (procedure-arity? . -> . normalized-arity?))
  (def-pred arity=? (procedure-arity? procedure-arity?))
  (def-pred arity-includes? (procedure-arity? procedure-arity?))
  (define ℓ:Λ (loc->ℓ (loc 'Λ 0 0 '())))
  )
