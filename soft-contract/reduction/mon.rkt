#lang typed/racket/base

(provide mon ↝.mon.v ↝.mon.c)

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt"
         "helpers.rkt"
         "continuation-if.rkt"
         "ap.rkt")

;; Monitor contract.
(define/memo (mon [l³ : Mon-Info] [ℓ : -ℓ] [W-C : -W¹] [W-V : -W¹]) : -⟦e⟧
  (match-define (-W¹ C _) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  
  (λ (M σ ℒ)
    (define Γ (-ℒ-cnd ℒ))
    (case (MσΓ⊢V∈C M σ Γ W-C W-V)
      [(✓)
       (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅)]
      [(✗)
       (values ⊥σ ∅ {set (-ΓE (-ℒ-cnd ℒ) (-blm l+ lo (list C) (list V)))} ∅)]
      [(?)
       (define f ; TODO: make them thunks inside this function instead?
         (cond
           [(-=>i? C)      mon-=>i     ]
           [(-St/C? C)     mon-struct/c]
           [(-x/C? C)      mon-x/c     ]
           [(-And/C? C)    mon-and/c   ]
           [(-Or/C?  C)    mon-or/c    ]
           [(-Not/C? C)    mon-not/c   ]
           [(-Vectorof? C) mon-vectorof]
           [(-Vector/C? C) mon-vector/c]
           [else           mon-flat    ]))
       ((f l³ ℓ W-C W-V) M σ ℒ)])))

(: mon-=>i : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-=>i l³ ℓ W-C W-V)
  (match-define (-W¹ (and guard (-=>i _ (-Clo xs _ _ _))) c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  
  (define arity
    (let ([b (-b (match xs
                   [(? list? xs) (length xs)]
                   [(-varargs zs z) (arity-at-least (length zs))]))])
      (-W¹ b b)))
  
  (λ (M σ ℒ)
    ;; Perform first-order checks for procedure?-ness and arity before wrapping
    (define Γ (-ℒ-cnd ℒ))
    (define-values (Γ₁ Γ₂) (Γ+/-W∋Ws M σ Γ -procedure?/W W-V))
    (define-values (Γ₁₁ Γ₁₂)
      (if Γ₁
          (let ([A (V-arity V)]
                [a (-?@ 'procedure-arity v)])
            (define W-a (-W¹ (if A (-b A) -●/V) a))
            (Γ+/-W∋Ws M σ Γ₁ -arity-includes?/W W-a arity))
          (values #f #f)))
    (define-set ΓWs : -ΓW)
    (define-set ΓEs : -ΓE)
    (define δσ : -Δσ ⊥σ)
    (when Γ₁₁
      (define α (-α.rng ℓ (-ℒ-hist ℒ)))
      (define Ar (-Ar guard (cons α v) l³))
      (ΓWs-add! (-ΓW Γ₁₁ (-W (list Ar) v)))
      (set! δσ (⊔ ⊥σ α V)))
    (when Γ₁₂
      (ΓEs-add! (-ΓE Γ₁₂ (-blm l+ lo (list (-W¹-V arity)) (list V)))))
    (when Γ₂
      (ΓEs-add! (-ΓE Γ₂ (-blm l+ lo (list 'procedure?) (list V)))))
    (values δσ ΓWs ΓEs ∅)))

(: mon-struct/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-struct/c l³ ℓ W-C W-V)
  (error "TODO"))

(: mon-x/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-x/c l³ ℓ W-C W-V)
  (error "TODO"))

(: mon-and/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
;; Monitor contract conjunction by decomposing into nesting checks
(define (mon-and/c l³ ℓ W-C W-V)
  (match-define (-W¹ (-And/C _ α₁ α₂) c) W-C)
  (match-define (list c₁ c₂) (-app-split c 'and/c 2))
  (λ (M σ ℒ)
    (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       ;; TODO: be careful `(mon ...)` can generate infinitely many ⟦e⟧s
       (((↝.mon.c l³ ℓ (-W¹ C₂ c₂)) (mon l³ ℓ (-W¹ C₁ c₁) W-V)) M σ ℒ))))

(: mon-or/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-or/c l³ ℓ W-C W-V)
  (error "TODO"))

(: mon-not/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
;; Monitor negation contract. It must be flat.
(define (mon-not/c l³ ℓ W-C W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ (and C (-Not/C α)) c) W-C)
  (match-define (-W¹ V _) W-V)
  (match-define (list c*) (-app-split c 'not/c 1))
  (define ⟦ℰ⟧
    (let ([⟦e⟧ₒₖ (ret-W¹ W-V)]
          [⟦e⟧ₑᵣ (blm l+ lo (list C) (list V))])
      (↝.if lo ⟦e⟧ₑᵣ ⟦e⟧ₒₖ)))
  (λ (M σ ℒ)
    (for*/ans ([C* (σ@ σ α)])
      (assert C* C-flat?)
      (define W-C* (-W¹ C* c*))
      ((⟦ℰ⟧ (ap lo 0 W-C* (list W-V))) M σ ℒ))))

(: mon-vectorof : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-vectorof l³ ℓ α V)
  (error "TODO"))

(: mon-vector/c : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
(define (mon-vector/c l³ ℓ αs V)
  (error "TODO"))

(: mon-flat : Mon-Info -ℓ -W¹ -W¹ → -⟦e⟧)
;; Monitor flat contract
(define (mon-flat l³ ℓ W-C W-V)
  (match-define (Mon-Info l+ _ lo) l³)
  (match-define (-W¹ C _) W-C)
  (match-define (-W¹ V _) W-V)
  (define ⟦ℰ⟧
    (let ([⟦e⟧ₒₖ (ret-W¹ W-V)]
          [⟦e⟧ₑᵣ (blm l+ lo (list C) (list V))])
      (↝.if lo ⟦e⟧ₒₖ ⟦e⟧ₑᵣ)))
  (⟦ℰ⟧ (ap lo 0 W-C (list W-V))))

(: ↝.mon.v : Mon-Info -ℓ (U -⟦e⟧ -W¹) → -⟦ℰ⟧)
;; Waiting on contract to monitor
(define ((↝.mon.v l³ ℓ Val) ⟦c⟧)
  (define lo (Mon-Info-src l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.mon.v l³ ℓ ℰ Val))
      (λ (σ* Γ* W)
        (match-define (-W Vs c) W)
        (with-guarded-arity 1 (lo Γ* Vs)
          (match-define (list C) Vs)
          (define W-C (-W¹ C c))
          ;; If target is evaluated, check it, otherwise evaluate it before checking
          (define ⟦mon⟧
            (cond [(-W¹? Val) (   mon   l³ ℓ W-C  Val)]
                  [else       ((↝.mon.c l³ ℓ W-C) Val)]))
          (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))
     (⟦c⟧ M σ ℒ))))

(: ↝.mon.c : Mon-Info -ℓ (U -⟦e⟧ -W¹) → -⟦ℰ⟧)
;; Waiting on value to monitor
(define ((↝.mon.c l³ ℓ Ctc) ⟦e⟧)
  (define lo (Mon-Info-src l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.mon.c l³ ℓ Ctc ℰ))
      (λ (σ* Γ* W)
        (match-define (-W Vs v) W)
        (with-guarded-arity 1 (lo Γ* Vs)
          (match-define (list V) Vs)
          (define W-V (-W¹ V v))
          ;; If contract is evaluated, check with it, otherwise evaluate it before checking
          (define ⟦mon⟧
            (cond [(-W¹? Ctc) (   mon   l³ ℓ Ctc  W-V)]
                  [else       ((↝.mon.v l³ ℓ W-V) Ctc)]))
          (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))
     (⟦e⟧ M σ ℒ))))

;; memoize these to avoid generating infinitely many compiled expressions
(define/memo (blm [l+ : Mon-Party] [lo : Mon-Party] [Cs : (Listof -V)] [Vs : (Listof -V)]) : -⟦e⟧
  (λ (M σ ℒ)
    (values ⊥σ ∅ {set (-ΓE (-ℒ-cnd ℒ) (-blm l+ lo Cs Vs))} ∅)))
