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
  (import prim-runtime^)
  (export)

  (def-pred procedure?)

  #;(def (apply ℓ Vs H φ Σ ⟦k⟧)
    #:init ()
    #:rest [Ws (listof any/c)] ; manual arity check instead
    (define l (ℓ-src ℓ))

    (: blm-for : -h (Listof -V^) -φ → (℘ -ς))
    (define (blm-for C Vs φ)
      (⟦k⟧ (blm/simp l 'apply (list C) Vs ℓ) H φ Σ))

    (: check-func-arity : -V (Listof -V^) -V^ -φ → (℘ -ς))
    ;; Make sure init arguments and rest args are compatible with the function's arity
    (define (check-func-arity V-func V-inits^ V-rest^ φ)
      (: blm-arity : Arity → (℘ -ς))
      (define (blm-arity a)
        (define blm-args (append V-inits^ (list V-rest^)))
        (define msg (string->symbol (format "~a argument(s)" a)))
        (define blm (blm/simp l 'apply (list msg) blm-args ℓ))
        (⟦k⟧ blm H φ Σ))

      (define-simple-macro (with-num-rest-args-check pred V-rest:id #:on-t e₁ #:on-f e₂)
        (let-values ([(ok? er?)
                      (for/fold ([ok? : Boolean #f] [er? : Boolean #f])
                                ([len (in-set (estimate-list-lengths (-Σ-σ Σ) (-φ-cache φ) V-rest))])
                        (if (pred len) (values #t er?) (values ok? #t)))])
          (∪ (if ok? e₁ ∅) (if er? e₂ ∅))))

      ;; turn estinate-list-lengths into 
      
      (define num-inits (length V-inits^))

      (match (V-arity V-func)
        [(? index? fixed-arity)
         (define num-remaining-args (- fixed-arity num-inits))
         (cond
           ;; Fewer init arguments than required, then try to retrieve in rest-arg for more
           [(<= 0 num-remaining-args)
            (for/union : (℘ -ς) ([V-rest (in-set V-rest^)])
               (with-num-rest-args-check (match-lambda
                                           [(? index? len) (equal? len num-remaining-args)]
                                           [(arity-at-least len) #|TODO|# #t])
                 V-rest
                 #:on-t (app/rest/unsafe ℓ V-func V-inits^ V-rest H φ Σ ⟦k⟧)
                 #:on-f (blm-arity fixed-arity)))]
           ;; More init arguments than required
           [else (blm-arity fixed-arity)])]
        [(arity-at-least arity.min)
         (define remaining-inits (- arity.min num-inits))
         (cond
           ;; init-args maybe too short, then retrieve some more from rest-arg
           [(<= 0 remaining-inits)
            (for/union : (℘ -ς) ([V-rest (in-set V-rest^)])
              (with-num-rest-args-check (match-lambda
                                          [(? index? len) (>= len remaining-inits)]
                                          [(arity-at-least len) (>= len remaining-inits)])
                V-rest
                #:on-t (app/rest/unsafe ℓ V-func V-inits^ V-rest H φ Σ ⟦k⟧)
                #:on-f (blm-arity arity.min)))]
           ;; init args more than enough
           [else
            (for/union : (℘ -ς) ([V-rest (in-set V-rest^)])
               (app/rest/unsafe ℓ V-func V-inits^ V-rest H φ Σ ⟦k⟧))])]
        [a
         (error 'apply "TODO: handle arity ~a" a)]))

    ;; Make sure there is at least the function and rest args
    (match Vs
      [(list V-func^ V-inits^s ... V-rest^)
       (define V-inits^ (cast V-inits^s (Listof -V^)))
       (for/union : (℘ -ς) ([V-func (in-set V-func^)])
          (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ (-Σ-σ Σ) φ 'procedure? {set V-func})]) : -ς
            #:true  (check-func-arity V-func V-inits^ V-rest^ φ₁)
            #:false (blm-for 'procedure? (list V-func^) φ₂)))]
      [_
       (define blm (blm-arity ℓ l (arity-at-least 2) Vs))
       (⟦k⟧ blm H φ Σ)]))
  
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
  #;(def (procedure-arity ℓ Vs H φ Σ ⟦k⟧)
    #:init ([V^ procedure?])
    (define Vₐ^ (for/set: : -V^ ([V (in-set V^)])
                  (match (V-arity V)
                    [(? values a) (-b a)]
                    [#f (-● ∅)])))
    (⟦k⟧ (list Vₐ^) H φ Σ))
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
