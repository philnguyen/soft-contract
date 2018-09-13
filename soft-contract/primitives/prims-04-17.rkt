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
  (import evl^ val^
          prim-runtime^ prover^
          step^ app^)
  (export)

  (def-pred procedure?)
  (define ℓ:apply (loc->ℓ (loc 'apply 0 0 '())))
  (def (apply Ts ℓ Φ^₀ Ξ₀ Σ)
    #:init ()
    #:rest [Ts (listof any/c)] ; manual arity check instead

    (: check-fun-arity : V W T^ Φ^ → (℘ Ξ))
    ;; Make sure init arguments and rest args are compatible with the function's arity
    (define (check-fun-arity Vₕ Tₓs Tᵣ Φ^₀) 
      (define num-inits (length Tₓs))
      (define Vₕ:arity (T-arity Vₕ))
      
      (define (blm-arity)
        (define msg (string->symbol (format "~a argument(s)" Vₕ:arity)))
        {set (Blm (ℓ-src ℓ) ℓ ℓ:apply (list msg) (append Tₓs (list Tᵣ)))})

      (define (go-with-rest [Vᵣ : V]) (app/rest/unsafe Vₕ Tₓs Vᵣ ℓ Φ^₀ Ξ₀ Σ))

      (: with-num-rest-args-check : ((U Arity #f) → Boolean) → V → (℘ Ξ))
      (define ((with-num-rest-args-check p?) Vᵣ)
        (define-values (ok? er?)
          (for/fold ([ok? : Boolean #f] [er? : Boolean #f])
                    ([len (in-set (estimate-list-lengths Σ Vᵣ))])
            (if (p? len) (values #t er?) (values ok? #t))))
        (∪ (if ok? (app/rest/unsafe Vₕ Tₓs Vᵣ ℓ Φ^₀ Ξ₀ Σ) ∅)
           (if er? (blm-arity) ∅)))
      
      (match Vₕ:arity
        [(? index? fixed-arity)
         (define num-remaining-args (- fixed-arity num-inits))
         (cond
           ;; Fewer init arguments than required, then try to retrieve in rest-arg for more
           [(<= 0 num-remaining-args)
            (set-union-map
             (with-num-rest-args-check
               (match-lambda
                 [(? index? len) (equal? len num-remaining-args)]
                 [(arity-at-least len) #|TODO|# #t]))
             (T->V Σ Φ^₀ Tᵣ))]
           ;; More init arguments than required
           [else (blm-arity)])]
        [(arity-at-least arity:min)
         (define remaining-inits (- arity:min num-inits))
         (cond
           ;; init-args maybe too short, then retrieve some more from rest-arg
           [(<= 0 remaining-inits)
            (set-union-map
             (with-num-rest-args-check
               (match-lambda
                 [(? index? len) (>= len remaining-inits)]
                 [(arity-at-least len) (>= len remaining-inits)]))
             (T->V Σ Φ^₀ Tᵣ))]
           ;; init args more than enough
           [(set? Tᵣ) (set-union-map go-with-rest Tᵣ)]
           [else (app/rest/unsafe Vₕ Tₓs Tᵣ ℓ Φ^₀ Ξ₀ Σ)])]
        [a
         (error 'apply "TODO: handle arity ~a" a)]))

    ;; Make sure there is at least the function and rest args
    (match Ts
      [(list Tₕ Tₓs ... Tᵣ)
       ((inst with-2-paths Ξ)
         (λ () (split-results Σ (R (list (T->V Σ Φ^₀ Tₕ)) Φ^₀) 'procedure?))
         (λ (R^)
           (define Tₓs* (cast Tₓs (Listof T^)))
           (for*/union : (℘ Ξ) ([Rᵢ (in-set R^)]
                                [Φ^ᵢ (in-value (R-_1 Rᵢ))]
                                [Vₕ (in-set (assert (car (R-_0 Rᵢ)) set?))])
             (check-fun-arity Vₕ Tₓs* Tᵣ Φ^ᵢ)))
         (λ (R^) (blm (ℓ-src ℓ) ℓ ℓ:Λ '(procedure?) (list Tₕ))))]
      [_
       (blm (ℓ-src ℓ) ℓ ℓ:apply (list (string->symbol "(arity-at-least/c 2)")) Ts)]))
  
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
  (def (procedure-arity W ℓ Φ^ Ξ₀ Σ)
    #:init ([Tₕ procedure?])
    (define Tₐ
      (if (set? Tₕ)
          (for/set : V^ ([Vₕ (in-set Tₕ)])
            (cond [(T-arity Vₕ) => -b]
                  [else (-● ∅)]))
          (S:@ 'procedure-arity (list Tₕ))))
    {set (ret! (R (list Tₐ) Φ^) Ξ₀ Σ)})
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
