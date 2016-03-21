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

(: mon : Mon-Info -W¹ -W¹ → -⟦e⟧)
;; Monitor contract.
(define (mon l³ W-C W-V)
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
       ((f l³ W-C W-V) M σ ℒ)])))

(: mon-=>i : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-=>i l³ W-C W-V)
  (error "TODO"))

(: mon-struct/c : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-struct/c l³ W-C W-V)
  (error "TODO"))

(: mon-x/c : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-x/c l³ W-C W-V)
  (error "TODO"))

(: mon-and/c : Mon-Info -W¹ -W¹ → -⟦e⟧)
;; Monitor contract conjunction by decomposing into nesting checks
(define (mon-and/c l³ W-C W-V)
  (match-define (-W¹ (-And/C _ α₁ α₂) c) W-C)
  (match-define (list c₁ c₂) (-app-split c 'and/c 2))
  (λ (M σ ℒ)
    (for*/ans ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       (error "TODO"))))

(: mon-or/c : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-or/c l³ W-C W-V)
  (error "TODO"))

(: mon-not/c : Mon-Info -W¹ -W¹ → -⟦e⟧)
;; Monitor negation contract. It must be flat.
(define (mon-not/c l³ W-C W-V)
  (match-define (-W¹ (-Not/C α) c) W-C)
  (match-define (list c*) (-app-split c 'not/c 1))
  (define ⟦e⟧ₒₖ (mk-⟦e⟧ₒₖ W-V))
  (define ⟦e⟧ₑᵣ (mk-⟦e⟧ₑᵣ l³ W-C W-V))
  (define lo (Mon-Info-src l³))
  (define ⟦ℰ⟧ (↝.if lo ⟦e⟧ₑᵣ ⟦e⟧ₒₖ))
  (λ (M σ ℒ)
    (for*/ans ([C* (σ@ σ α)])
      (assert C* C-flat?)
      (define W-C* (-W¹ C* c*))
      ((⟦ℰ⟧ (ap lo 0 W-C* (list W-V))) M σ ℒ))))

(: mon-vectorof : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-vectorof l³ α V)
  (error "TODO"))

(: mon-vector/c : Mon-Info -W¹ -W¹ → -⟦e⟧)
(define (mon-vector/c l³ αs V)
  (error "TODO"))

(: mon-flat : Mon-Info -W¹ -W¹ → -⟦e⟧)
;; Monitor flat contract
(define (mon-flat l³ W-C W-V)
  (define ⟦e⟧ₒₖ (mk-⟦e⟧ₒₖ W-V))
  (define ⟦e⟧ₑᵣ (mk-⟦e⟧ₑᵣ l³ W-C W-V))
  (define lo (Mon-Info-src l³))
  ((↝.if lo ⟦e⟧ₒₖ ⟦e⟧ₑᵣ) (ap lo 0 W-C (list W-V))))

(: ↝.mon.v : Mon-Info (U -⟦e⟧ -W¹) → -⟦ℰ⟧)
;; Waiting on contract to monitor
(define ((↝.mon.v l³ Val) ⟦c⟧)
  (define lo (Mon-Info-src l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.mon.v l³ ℰ Val))
      (λ (σ* Γ* W)
        (match-define (-W Vs c) W)
        (with-guarded-arity 1 (lo Γ* Vs)
          (match-define (list C) Vs)
          (define W-C (-W¹ C c))
          ;; If target is evaluated, check it, otherwise evaluate it before checking
          (define ⟦mon⟧
            (cond [(-W¹? Val) (   mon   l³ W-C  Val)]
                  [else       ((↝.mon.c l³ W-C) Val)]))
          (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))
     (⟦c⟧ M σ ℒ))))

(: ↝.mon.c : Mon-Info (U -⟦e⟧ -W¹) → -⟦ℰ⟧)
;; Waiting on value to monitor
(define ((↝.mon.c l³ Ctc) ⟦e⟧)
  (define lo (Mon-Info-src l³))
  (λ (M σ ℒ)
    (apply/values
     (acc
      σ
      (λ (ℰ) (-ℰ.mon.c l³ Ctc ℰ))
      (λ (σ* Γ* W)
        (match-define (-W Vs v) W)
        (with-guarded-arity 1 (lo Γ* Vs)
          (match-define (list V) Vs)
          (define W-V (-W¹ V v))
          ;; If contract is evaluated, check with it, otherwise evaluate it before checking
          (define ⟦mon⟧
            (cond [(-W¹? Ctc) (   mon   l³ Ctc  W-V)]
                  [else       ((↝.mon.v l³ W-V) Ctc)]))
          (⟦mon⟧ M σ* (-ℒ-with-Γ ℒ Γ*)))))
     (⟦e⟧ M σ ℒ))))

;; memoize these to avoid generating infinitely many compiled expressions
(define mk-⟦e⟧ₒₖ
  (with-memo (-W¹ → -⟦e⟧)
    (λ (W-V)
      (match-define (-W¹ V v) W-V)
      (λ (M σ ℒ)
        (values ⊥σ {set (-ΓW (-ℒ-cnd ℒ) (-W (list V) v))} ∅ ∅)))))
(define mk-⟦e⟧ₑᵣ
  (with-memo (Mon-Info -W¹ -W¹ → -⟦e⟧)
    (λ (l³ W-C W-V)
      (define C (-W¹-V W-C))
      (define V (-W¹-V W-V))
      (match-define (Mon-Info l+ _ lo) l³)
      (λ (M σ ℒ)
        (values ⊥σ ∅ {set (-ΓE (-ℒ-cnd ℒ) (-blm l+ lo (list C) (list V)))} ∅)))))
