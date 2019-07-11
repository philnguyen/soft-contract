#lang typed/racket/base

(provide exec^
         evl^
         app^
         mon^
         hv^
         gc^
         termination^
         with-collapsed with-collapsed/R
         with-collapsing with-collapsing/R
         with-each-path
         for/ans
         log-scv-eval-debug)

(require (for-syntax racket/base
                     (only-in racket/list append-map)
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/set
         typed/racket/unit
         bnf
         unreachable
         intern
         set-extras
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         ) 

;; HACK: Errors in the object language is tracked through a side channel `err!`
;; in the meta-language. This is ugly and prevents expressing error handling,
;; but simplifies several thigns and is sufficient for now.
(define-signature exec^ 
  ([exec : ((U E -prog) → (Values (℘ Err) $))]
   [ref-$! : ($:Key (→ R) → R)]
   [err! : ((U (℘ Err) Err) → Void)]
   [current-module : (Parameterof -l)]
   [current-MS : (Parameterof (Option MS))]
   [current-app : (Parameterof (Option CP))]
   [blm : (-l ℓ ℓ W W → (℘ Blm))]
   [fold-ans : (∀ (X) (X → R) (℘ X) → R)]
   [fold-ans/collapsing : (∀ (X) Σ (X → R) (℘ X) → R)]
   [with-split-Σ : (Σ V W (W ΔΣ → R) (W ΔΣ → R) → R)]
   [make-renamings : ((U (Listof Symbol) -formals) W → Renamings)] ; FIXME move?
   [rename : (Renamings → (U T -prim) → (Option (U T -prim)))] ; FIXME move?
   [fix-return : (Renamings Σ R → R)]
   [db:iter? : (Parameterof Boolean)]
   [db:max-steps : (Parameterof (Option Index))]
   [db:depth : (Parameterof Natural)]))

;; Σ ⊢ E ⇓ A , ΔΣ
(define-signature evl^
  ([evl-prog : (-prog → (Option ΔΣ))]
   [evl : (Σ E → R)]))

;; Σ ⊢ V V… ⇓ᵃ A , ΔΣ
(define-signature app^
  ([app : (Σ ℓ D W → R)]
   [app/rest : (Σ ℓ D W D → R)]
   [st-ac-● : (-𝒾 Index (℘ P) Σ → V^)]))

;; Σ ⊢ V V ⇓ᵐ A , ΔΣ
(define-signature mon^
  ([mon : (Σ Ctx D D → R)]
   [mon* : (Σ Ctx W W → R)]))

(define-signature hv^
  ([leak : (Σ γ:hv V^ → R)]
   [gen-havoc-expr : ((Listof -module) → E)]
   [behavioral? : (V Σ → Boolean)]))

(define-signature termination^
  ([update-M : (Σ M CP CP W → (Option M))]
   #;[check-point : (V → CP)]))

(define-signature gc^
  ([gc : ([(℘ (U α T)) Σ] [Σ] . ->* . Σ)]
   [clear-live-set-cache! : (→ Void)]
   [gc-R : ((℘ (U α T)) Σ R → R)]
   [V-root : (V → (℘ (U α T)))]
   [D-root : (D → (℘ (U α T)))]
   [W-root : (W → (℘ (U α T)))]
   [E-root : (E → (℘ γ))]
   [T-root : (T → (℘ T))]))

(define-syntax with-collapsed
  (syntax-parser
    [(_ [?x:expr e:expr]
        (~optional (~seq #:fail fail:expr) #:defaults ([fail #'#f]))
        body:expr ...)
     #'(match e
         [(? values ?x) (let-values () body ...)]
         [#f fail])]))
(define-syntax-rule (with-collapsed/R [?x e] body ...)
  (with-collapsed [?x e] #:fail ⊥R body ...))

(define-syntax with-collapsing
  (syntax-parser
    [(_ Σ [(ΔΣ:id Ws) e:expr]
        (~optional (~seq #:fail fail:expr) #:defaults ([fail #'#f]))
        body:expr ...)
     (with-syntax ([collapse-R (format-id #'e "collapse-R")])
       #'(let ([r e])
           (match (collapse-R Σ r)
             [(cons Ws ΔΣ) body ...]
             [#f fail])))]))
(define-syntax-rule (with-collapsing/R Σ [(ΔΣ Ws) e] body ...)
  (with-collapsing Σ [(ΔΣ Ws) e] #:fail ⊥R body ...))

(define-syntax with-each-path
  (syntax-parser
    [(with-each-path ([(ΔΣᵢ Wᵢ) eᵢ] ...) body ...)
     (with-syntax ([R⊔ (format-id #'with-each-path "R⊔")])
       (define mk-clause
         (syntax-parser
           [(ΔΣᵢ Wᵢ eᵢ)
            (list
             #'[(Wᵢ ΔΣsᵢ) (in-hash eᵢ)]
             #'[ΔΣᵢ : ΔΣ (in-set ΔΣsᵢ)])]))
       #`(for*/fold ([r : R ⊥R])
                    (#,@(append-map mk-clause (syntax->list #'([ΔΣᵢ Wᵢ eᵢ] ...))))
           (R⊔ r (let () body ...))))]))

(define-syntax for/ans
  (syntax-parser
    [(for/ans (clauses ...) body ...)
     (with-syntax ([R⊔ (format-id #'for/ans "R⊔")])
       #'(for/fold ([r : R ⊥R]) (clauses ...)
           (R⊔ r (let () body ...))))]))

(define-logger scv-eval)
