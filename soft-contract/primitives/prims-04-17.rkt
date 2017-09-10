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
         racket/generator
         racket/random
         racket/format
         racket/splicing
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/debug.rkt"
         "../utils/pretty.rkt"
         (except-in "../ast/signatures.rkt" normalize-arity arity-includes?)
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../reduction/signatures.rkt"
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
  (import prim-runtime^ proof-system^ local-prover^ widening^ app^ val^ pc^)
  (export)

  (def-pred procedure?)

  (def (apply ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)] ; manual arity check instead
    (define l (ℓ-src ℓ))

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
                                ([len (in-set (estimate-list-lengths (-Σ-σ Σ) (-W¹-V W-rest)))])
                        (if (pred len) (values #t er?) (values ok? #t)))])
          (∪ (if ok? e₁ ∅) (if er? e₂ ∅))))

      ;; turn estinate-list-lengths into 
      
      (define num-inits (length W-inits))
      (match-define (-W¹ V-func t-func) W-func)

      (match (V-arity V-func)
        [(? index? fixed-arity)
         (define num-remaining-args (- fixed-arity num-inits))
         (cond
           ;; Fewer init arguments than required, then try to retrieve in rest-arg for more
           [(<= 0 num-remaining-args)
            (with-num-rest-args-check (match-lambda
                                        [(? index? len) (equal? len num-remaining-args)]
                                        [(arity-at-least len) #|TODO|# #t])
              #:on-t (app/rest/unsafe ℓ W-func W-inits W-rest $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
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
              #:on-t (app/rest/unsafe ℓ W-func W-inits W-rest $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
              #:on-f (blm-arity arity.min))]
           ;; init args more than enough
           [else
            (app/rest/unsafe ℓ W-func W-inits W-rest $ Γ ⟪ℋ⟫ Σ ⟦k⟧)])]
        [a
         (error 'apply "TODO: handle arity ~a" a)]))

    ;; Make sure there is at least the function and rest args
    (match Ws
      [(list W-func W-inits ... W-rest)
       (Γ+/-oW/handler
        (check-func-arity W-func (cast W-inits (Listof -W¹)) W-rest)
        (blm-for 'procedure? (list (-W¹-V W-func)))
        (-Σ-σ Σ) Γ 'procedure? W-func)]
      [_
       (define blm (blm-arity ℓ l (arity-at-least 2) (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
  
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
  (def (procedure-arity ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #:init ([W procedure?])
    (match-define (-W¹ V s) W)
    (define sₐ (?t@ 'procedure-arity s))
    (cond [(V-arity V)
           =>
           (λ ([a : Arity])
             (⟦k⟧ (-W (list (-b a)) sₐ) $ Γ ⟪ℋ⟫ Σ))]
          [else (⟦k⟧ (-W (list (+●)) sₐ) $ Γ ⟪ℋ⟫ Σ)]))
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
  
  )
