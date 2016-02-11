#lang typed/racket/base

(require
 racket/match racket/set
 "../utils/set.rkt" "../utils/function.rkt" "../utils/map.rkt"
 "../ast/definition.rkt"
 "runtime.rkt" "continuation.rkt")

(: ev : -M -Ξ -σ -ℬ → (Values -ΔM -ΔΞ -Δσ))
(define (ev M Ξ σ ℬ)
  (match-define (-ℬ ⟦e⟧ _) ℬ)
  (apply/values (collect M Ξ ℬ) (⟦e⟧ M σ ℬ)))

(: co : -M -Ξ -σ -Co → (Values -ΔM -ΔΞ -Δσ))
(define (co M Ξ σ Co)
  (match-define (-Co (-ℛ ℬ ℋ) As) Co)
  (apply/values (collect M Ξ ℬ) ((ℰ⟦_⟧ ℋ As) M σ ℬ)))

(: ⟦_⟧ : -e → -⟦e⟧)
;; Compile expresion to mapping from store to (potentially suspended) results
(define (⟦_⟧ e)
  (match e
    [(-λ xs e*)
     (define ⟦e*⟧ (⟦_⟧ e*))
     (λ (_M _σ ℬ)
       (match-define (-ℬ _ ρ) ℬ)
       (values ⊥σ {set (-A ⊤Γ (-W (list (-Clo xs ⟦e*⟧ ρ)) e))} ∅))]
    [(-case-λ body) (error '⟦_⟧ "TODO: case-λ")]
    [(? -prim? p)
     (λ _
       (values ⊥σ {set (-A ⊤Γ (-W (list p) p))} ∅))]
    [(-x x)
     (λ (M σ ℬ)
       (match-define (-ℬ _ ρ) ℬ)
       (define e-x (canonicalize ρ x))
       (define As
         (for/set: : (℘ -A) ([V (hash-ref σ (ρ@ ρ x))])
           ;; TODO: remove spurious values
           (define A
             (case V
               [(undefined) ; FIXME hack
                (-blm 'TODO 'Λ (-st-p (-struct-info (-id 'defined 'Λ) 1 ∅)) (list 'undefined))]
               [else (-W (list V) e-x)]))
           (-A ⊤Γ A)))
       (values ⊥σ As ∅))]
    [(and ref (-ref (and id (-id name l-from)) l-ctx pos))
     (λ (M σ ℬ)
       (cond
         [(equal? l-from l-ctx)
          (define As
            (for/set: : (℘ -A) ([V (hash-ref σ (-α.def id))])
              (define s (if (-o? V) V ref))
              (-A ⊤Γ (-W (list V) s))))
          (values ⊥σ As ∅)]
         [else
          (define Vs (hash-ref σ (-α.def id)))
          (define Cs (hash-ref σ (-α.ctc id)))
          (error '⟦_⟧ "TODO: mon")]))]
    [(-@ f xs l)
     ((⟦-ℰ.@⟧ '() (map ⟦_⟧ xs) l) (⟦_⟧ f))]
    [(-if e₀ e₁ e₂)
     ((⟦-ℰ.if⟧ (⟦_⟧ e₁) (⟦_⟧ e₂)) (⟦_⟧ e₀))]))

(: ℰ⟦_⟧ : -ℋ (℘ -A) → -⟦e⟧)
;; Plug results `As` into hole `ℰ` and resume computation
;; Stacks `ℰ` are also finite, but I can't compile them away ahead of time because they depend on `V`
;; computed at "runtime". Using functions instead of flat values to represent `ℰ` may genereate
;; infinitely many equivalent but distinct (Racket-level) functions.
;; Memoization might help, but I doubt it speeds up anything.
;; So I'll keep things simple for now.
(define (ℰ⟦_⟧ ℋ As)
  (match-define (-ℋ Γ f param->arg ℰ) ℋ)
  ;; TODO: use `Γ`, `f`, and `param->arg` to filter out spurious returns from `As`
  (: propagate-returns : (℘ -A) → (℘ -A))
  (define (propagate-returns As) (error "TODO"))
  (define As* (propagate-returns As))

  (let go ([ℰ : -ℰ ℰ])
    (match ℰ
      ['□ (λ _ (values ⊥σ As* ∅))]
      [(-ℰ.if ℰ* ⟦e₁⟧ ⟦e₂⟧)
       ((⟦-ℰ.if⟧ ⟦e₁⟧ ⟦e₂⟧) (go ℰ*))]
      [(-ℰ.@ WVs ℰ* ⟦e⟧s loc)
       ((⟦-ℰ.@⟧ WVs ⟦e⟧s loc) (go ℰ*))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: collect : -M -Ξ -ℬ → -Δσ (℘ -A) (℘ -ℐ) → (Values -ΔM -ΔΞ -Δσ))
;; Collect evaluation results into store deltas
(define ((collect M Ξ ℬ) δσ As ℐs)
  
  (define δM : -ΔM
    (let ([ΔAs (set-subtract (m@ M ℬ) As)])
      (if (set-empty? ΔAs) ⊥M (hash ℬ ΔAs))))
  
  (define δΞ
    (for*/fold ([δΞ : -ΔΞ ⊥Ξ])
               ([ℐ ℐs]
                [ℋ  (in-value (-ℐ-hole ℐ))]
                [ℬ* (in-value (-ℐ-target ℐ))]
                [ℛ  (in-value (-ℛ ℬ ℋ))]
                #:unless (m∋ Ξ ℬ* ℛ))
      (⊔ δΞ ℬ* ℛ)))
  
  (values δM δΞ δσ))
