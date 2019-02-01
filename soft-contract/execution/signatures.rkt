#lang typed/racket/base

(provide exec^
         evl^
         app^
         mon^
         hv^
         gc^
         with-collapsed with-collapsed/R
         with-collapsing with-collapsing/R
         with-each-path
         with-pre
         for/ans)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/set
         typed/racket/unit
         bnf
         unreachable
         intern
         set-extras
         (only-in "../utils/map.rkt" m⊔)
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         ) 

(define-signature exec^ 
  ([exec : ((U E -prog) → (Values (℘ Err) $))]
   [ref-$! : ($:Key (→ (Values R (℘ Err))) → (Values R (℘ Err)))]
   [current-module : (Parameterof -l)]
   [just : ([(U V V^ W)] [ΔΣ] . ->* . (Values R (℘ Err)))]
   [err : (Err → (Values R (℘ Err)))] 
   [fold-ans : (∀ (X) (X → (Values R (℘ Err))) (℘ X) → (Values R (℘ Err)))]
   [ans-map : ((ΔΣ W^ → (Values R (℘ Err))) R → (Values R (℘ Err)))]
   [with-split-Σ : (Σ V W
                      (W ΔΣ → (Values R (℘ Err)))
                      (W ΔΣ → (Values R (℘ Err)))
                      → (Values R (℘ Err)))]
   [db:iter? : (Parameterof Boolean)]
   [db:max-steps : (Parameterof (Option Index))]
   [db:depth : (Parameterof Natural)]))

;; Σ ⊢ E ⇓ A , ΔΣ
(define-signature evl^
  ([evl-prog : (-prog → (Values (Option ΔΣ) (℘ Err)))]
   [evl : (Σ E → (Values R (℘ Err)))]))

;; Σ ⊢ V V… ⇓ᵃ A , ΔΣ
(define-signature app^
  ([app : (Σ ℓ V^ W → (Values R (℘ Err)))]
   [app/rest : (Σ ℓ V^ W V^ → (Values R (℘ Err)))]))

;; Σ ⊢ V V ⇓ᵐ A , ΔΣ
(define-signature mon^
  ([mon : (Σ Ctx V^ V^ → (Values R (℘ Err)))]
   [mon* : (Σ Ctx W W → (Values R (℘ Err)))]))

(define-signature hv^
  ([hv : (Σ γ:hv → (Values R (℘ Err)))]
   [gen-havoc-expr : ((Listof -module) → E)]))

(define-signature gc^
  ([gc : ((℘ (U T:@ α)) Σ → Σ)]
   [V-root : (V → (℘ (U T:@ α)))]
   [V^-root : (V^ → (℘ (U T:@ α)))]
   [W-root : (W → (℘ (U T:@ α)))]
   [E-root : (E → (℘ γ))]))

(define-syntax with-collapsed
  (syntax-parser
    [(_ [?x:expr e:expr]
        (~optional (~seq #:fail fail:expr) #:defaults ([fail #'#f]))
        body:expr ...)
     #'(match/values e
         [((? values ?x) es)
          (define-values (r* es*) (let-values () body ...))
          (values r* (∪ es es*))]
         [(#f es) (values fail es)])]))
(define-syntax-rule (with-collapsed/R [?x e] body ...)
  (with-collapsed [?x e] #:fail ⊥R body ...))

(define-syntax with-collapsing
  (syntax-parser
    [(_ [(ΔΣ:id Ws) e:expr]
        (~optional (~seq #:fail fail:expr) #:defaults ([fail #'#f]))
        body:expr ...)
     (with-syntax ([collapse-R (format-id #'e "collapse-R")])
       #'(let-values ([(r es) e])
           (match (collapse-R r)
             [(cons Ws ΔΣ)
              (define-values (r* es*) (let () body ...))
              (values r* (∪ es es*))]
             [#f (values fail es)])))]))
(define-syntax-rule (with-collapsing/R [(ΔΣ Ws) e] body ...)
  (with-collapsing [(ΔΣ Ws) e] #:fail ⊥R body ...))

(define-syntax-rule (with-each-path [(ΔΣ₀ Ws₀) e] body ...)
  (let-values ([(r₀ es₀) e])
    (for/fold ([r* : R ⊥R] [es* : (℘ Err) es₀])
              ([(ΔΣ₀ Ws₀) (in-hash r₀)])
      (define-values (r₁ es₁) (let () body ...))
      ;; TODO replace m⊔ with more efficient one
      (values (m⊔ r* r₁) (∪ es* es₁)))))

(define-syntax with-pre
  (syntax-parser
    [(_ ΔΣ e)
     (with-syntax ([ΔΣ⧺R (format-id #'e "ΔΣ⧺R")])
       #'(let-values ([(r es) e])
           (values (ΔΣ⧺R ΔΣ r) es)))]))

(define-syntax-rule (for/ans (clauses ...) body ...)
  (for/fold ([r : R ⊥R] [es : (℘ Err) ∅]) (clauses ...)
    (define-values (rᵢ esᵢ) (let () body ...))
    (values (m⊔ r rᵢ) (∪ es esᵢ))))

(define-syntax-rule (for*/ans (clauses ...) body ...)
  (for*/fold ([r : R ⊥R] [es : (℘ Err) ∅]) (clauses ...)
    (define-values (rᵢ esᵢ) (let () body ...))
    (values (m⊔ r rᵢ) (∪ es esᵢ))))
