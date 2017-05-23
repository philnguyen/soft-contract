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
         racket/set
         racket/flonum
         racket/fixnum
         racket/extflonum
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         "../utils/pretty.rkt"
         (except-in "../ast/definition.rkt" normalize-arity arity-includes?)
         "../ast/shorthands.rkt"
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         "def-prim.rkt"
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide prims-04-17@)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 4.17 Procedures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-unit prims-04-17@
  (import prim-runtime^ proof-system^ widening^ app^ val^ pc^ sto^ instr^)
  (export)

  (def-pred procedure?)

  (def-ext (apply $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-Σ σ _ M) Σ)
    (define-values (ℓ l) (unpack-ℒ ℒ))

    (: blm-for : -V (Listof -V) → -Γ → (℘ -ς))
    (define ((blm-for C Vs) Γ)
      (⟦k⟧ (-blm l 'apply (list C) Vs ℓ) $ Γ ⟪ℋ⟫ Σ))

    (: check-func-arity : -W¹ (Listof -W¹) -W¹ → -Γ → (℘ -ς))
    ;; Make sure init arguments and rest args are compatible with the function's arity
    (define ((check-func-arity W-func W-inits W-rest) Γ)
      
      (: blm-arity : Arity → (℘ -ς))
      (define (blm-arity a)
        (define blm-args (append (map -W¹-V W-inits) (list (-W¹-V W-rest))))
        (define msg (string->symbol (format "~a argument(s)" a)))
        (define blm (-blm l 'apply (list msg) blm-args ℓ))
        (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

      (define-simple-macro (with-num-rest-args-check pred #:on-t e₁ #:on-f e₂)
        (let-values ([(ok? er?)
                      (for/fold ([ok? : Boolean #f] [er? : Boolean #f])
                                ([len (in-set (estimate-list-lengths σ (-W¹-V W-rest)))])
                        (if (pred len) (values #t er?) (values ok? #t)))])
          (∪ (if ok? e₁ ∅) (if er? e₂ ∅))))
      
      (define num-inits (length W-inits))
      (match-define (-W¹ V-func t-func) W-func)

      (match (V-arity V-func)
        [(? index? fixed-arity)
         (define num-remaining-args (- fixed-arity num-inits))
         (cond
           ;; Fewer init arguments than required, then try to retrieve in rest-arg for more
           [(<= 0 num-remaining-args)
            (with-num-rest-args-check (λ (len) (equal? len num-remaining-args))
              #:on-t (app/rest/unsafe $ ℒ W-func W-inits W-rest Γ ⟪ℋ⟫ Σ ⟦k⟧)
              #:on-f (blm-arity fixed-arity))]
           ;; More init arguments than required
           [else (blm-arity fixed-arity)])]
        [(arity-at-least arity.min)
         (define remaining-inits (- arity.min num-inits))
         (cond
           ;; init-args maybe too short, then retrieve some more from rest-arg
           [(<= 0 remaining-inits)
            (with-num-rest-args-check (match-lambda
                                        [(? index? len) (>= len remaining-inits)]
                                        [(arity-at-least len) (>= len remaining-inits)])
              #:on-t (app/rest/unsafe $ ℒ W-func W-inits W-rest Γ ⟪ℋ⟫ Σ ⟦k⟧)
              #:on-f (blm-arity arity.min))]
           ;; init args more than enough
           [else
            (app/rest/unsafe $ ℒ W-func W-inits W-rest Γ ⟪ℋ⟫ Σ ⟦k⟧)])]
        [a
         (error 'apply "TODO: handle arity ~a" a)]))

    ;; Make sure there is at least the function and rest args
    (match Ws
      [(list W-func W-inits ... W-rest)
       (MΓ+/-oW/handler
        (check-func-arity W-func (cast W-inits (Listof -W¹)) W-rest)
        (blm-for 'procedure? (list (-W¹-V W-func)))
        M σ Γ 'procedure? W-func)]
      [_
       (define blm (blm-arity ℓ l (arity-at-least 2) (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
  
  (def-prim/todo compose ; FIXME uses
    ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any)))
  (def-prim/todo compose1 ; FIXME uses
    ((any/c . -> . any) (any/c . -> . any/c) . -> . (any/c . -> . any)))
  (def-prim/todo procedure-rename
    (procedure? symbol? . -> . procedure?))
  (def-prim/todo procedure->method
    (procedure? . -> . procedure?))
  (def-pred procedure-closure-contents-eq? (procedure? procedure?))

  ;; 4.17.1 Keywords and Arity
  ;[keyword-apply #|FIXME uses|#]
  (def-prim/custom (procedure-arity ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W procedure?])
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'procedure-arity s))
    (cond [(V-arity V) => (λ ([a : Arity]) {set (-ΓA (-Γ-facts Γ) (-W (list (-b a)) sₐ))})]
          [else {set (-ΓA (-Γ-facts Γ) (-W (list (+●)) sₐ))}]))
  (def-pred procedure-arity?)
  {def-pred procedure-arity-includes? (procedure? exact-nonnegative-integer?)} ; FIXME uses
  (def-prim/todo procedure-reduce-arity
    (procedure? procedure-arity? . -> . procedure?))
  #;[procedure-keywords ; FIXME listof
     (procedure? . -> . (values (listof keyword?) (or/c (listof keyword?) not)))]
  #;[make-keyword-procedure ; FIXME uses
     ((((listof keyword?) list?) () #:rest list? . ->* . any) . -> . procedure?)]
  #;[procedure-reduce-keyword-arity ; FIXME listof
     (procedure? procedure-arity? (listof keyword?) (or/c (listof keyword?) not)
                 . -> . procedure?)]
  (def-pred arity-at-least?)
  (def-prim/todo arity-at-least (exact-nonnegative-integer? . -> . arity-at-least?))
  (def-prim/todo arity-at-least-value (arity-at-least? . -> . exact-nonnegative-integer?))
  (def-alias make-arity-at-least arity-at-least)
  (def-opq prop:procedure struct-type-property?)
  [def-pred procedure-struct-type? (struct-type?)]
  (def-prim/todo procedure-extract-target
    (procedure? . -> . (or/c procedure? not)))
  (def-opq prop:arity-string struct-type-property?)
  (def-opq prop:checked-procedure struct-type-property?)
  (def-prim/todo checked-procedure-check-and-extract
    (struct-type? any/c (any/c any/c any/c . -> . any/c) any/c any/c . -> . any/c))

  ;; 4.17.2 Reflecting on Primitives
  (def-pred primitive?)
  (def-pred primitive-closure?)
  (def-prim/todo primitive-result-arity
    (primitive? . -> . procedure-arity?))

  ;; 4.17.3 Additional Higher-Order Functions
  (def-prim/custom (identity ⟪ℋ⟫ ℒ Σ Γ Ws)
    #:domain ([W any/c])
    (match-define (-W¹ V s) W)
    {set (-ΓA (-Γ-facts Γ) (-W (list V) s))})
  (def-prim/todo const (any . -> . procedure?))
  (def-prim/todo negate (procedure? . -> . procedure?))
  ;[curry ] FIXME
  ;[curryr] FIXME
  (def-pred/todo normalized-arity?)
  (def-prim/todo normalize-arity ; FIXME dependency
    (procedure-arity? . -> . normalized-arity?))
  (def-pred arity=? (procedure-arity? procedure-arity?))
  (def-pred arity-includes? (procedure-arity? procedure-arity?))
  
  )
