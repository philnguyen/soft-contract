#lang typed/racket/base

(provide run-file havoc-file run-e)

(require racket/set
         racket/match
         racket/list
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../parse/main.rkt"
         "../runtime/main.rkt"
         "../proof-relation/main.rkt" #;(only-in "../proof-relation/ext.rkt" miss/total)
         "compile/utils.rkt"
         "compile/kontinuation.rkt"
         "compile/main.rkt"
         "init.rkt"
         )

(: run-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (run-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define-values (σ₁ _) (𝑰 (list m)))
    (run (↓ₘ m) σ₁)))

(: havoc-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (havoc-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define-values (σ₁ e₁) (𝑰 (list m)))
    (run (↓ₚ (list m) e₁) σ₁)))

(: run-e : -e → (Values (℘ -ΓA) -Σ))
(define (run-e e)
  (with-initialized-static-info
    (define-values (σ₀ _) (𝑰 '()))
    (run (↓ₑ 'top e) σ₀)))

(define-type Ctx (List (HashTable -⟪α⟫ (℘ -V)) (HashTable -αₖ (℘ -κ))))

(: run : -⟦e⟧! -σ → (Values (℘ -ΓA) -Σ))
(define (run ⟦e⟧! σ)
  (define seen : (HashTable -ς Ctx) (make-hash))
  (define αₖ₀ : -αₖ (-ℬ '() ⟦e⟧! ⊥ρ))
  (define Σ (-Σ σ (⊥σₖ αₖ₀) (⊥M)))
  (define root₀ ; all addresses to top-level definitions are conservatively active
    (for/fold ([root₀ : (℘ -⟪α⟫) ∅eq]) ([𝒾 (top-levels)])
      (set-add (set-add root₀ (-α->-⟪α⟫ (-α.def 𝒾))) (-α->-⟪α⟫ (-α.wrp 𝒾)))))

  (: ς-vsn : -ς → Ctx)
  (define ς-vsn
    (match-let ([(-Σ (-σ mσ _ _) mσₖ _) Σ])
      (λ (ς)
        (define vsn-σ  (hash-copy/spanning* mσ (∪ (ς->⟪α⟫s ς mσₖ) root₀) V->⟪α⟫s))
        (define vsn-σₖ (m↓ mσₖ (ς->αₖs ς mσₖ)))
        (list vsn-σ vsn-σₖ))))

  (let touch! ([ς : -ς (-ς↑ αₖ₀ ⊤Γ ⟪ℋ⟫∅)] [d : Natural 0])
    (define d* (+ 1 d))
    (write-char #\o)
    (define i : Natural 0)
    (for ([ς* (in-set (↝! ς Σ))])
      (define vsn (ς-vsn ς*))
      (unless (equal? (hash-ref seen ς* #f) vsn)
        (hash-set! seen ς* vsn)
        (when (> i 0)
          (write-char #\newline)
          (for ([_ (in-range d*)]) (write-char #\space)))
        (set! i (+ 1 i))
        (touch! ς* d*))))
  (printf "~n")

  (match-let ([(-Σ σ σₖ M) Σ])
    (values (M@ M αₖ₀) Σ)))

(: ς->⟪α⟫s : -ς (HashTable -αₖ (℘ -κ)) → (℘ -⟪α⟫))
;; Compute the root set for value addresses of this state
(define (ς->⟪α⟫s ς σₖ)
  (match ς
    [(-ς↑ αₖ _ _)
     (define αs₀
       (match αₖ
         [(-ℬ _ _ ρ) (->⟪α⟫s ρ)]
         [(-ℳ _ _ _ (-W¹ C _) (-W¹ V _)) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]
         [(-ℱ _ _ _ (-W¹ C _) (-W¹ V _)) (∪ (->⟪α⟫s C) (->⟪α⟫s V))]))
     (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]
    [(-ς↓ αₖ _ A) ; if it's a "return" state, don't care about block content (e.g. `ρ`)
     (define αs₀ (if (-W? A) (->⟪α⟫s A) ∅eq))
     (∪ αs₀ (αₖ->⟪α⟫s αₖ σₖ))]))

(: ς->αₖs : -ς (HashTable -αₖ (℘ -κ)) → (℘ -αₖ))
;; Compute all relevant stack addresses
(define (ς->αₖs ς σₖ)
  (define αₖ
    (match ς
      [(-ς↑ αₖ _ _) αₖ]
      [(-ς↓ αₖ _ _) αₖ]))
  (span-σₖ σₖ αₖ))

(: ↝! : -ς -Σ → (℘ -ς))
(define (↝! ς Σ)
  (if (-ς↑? ς) (↝↑! ς Σ) (↝↓! ς Σ)))

(: ↝↑! : -ς↑ -Σ → (℘ -ς))
(define (↝↑! ς Σ)
  (match-define (-ς↑ αₖ Γ ⟪ℋ⟫) ς)
  (define ⟦k⟧ (rt αₖ))
  (match αₖ
    [(-ℬ _ ⟦e⟧! ρ)        (⟦e⟧! ρ $∅ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-ℳ _ l³ ℓ W-C W-V) (mon l³ $∅ ℓ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-ℱ _ l  ℓ W-C W-V) (flat-chk l $∅ ℓ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [_ (error '↝↑ "~a" αₖ)]))

(: ↝↓! : -ς↓ -Σ → (℘ -ς))
(define (↝↓! ς Σ)
  (match-define (-Σ _ σₖ M) Σ)
  (match-define (-ς↓ αₖ Γₑₑ A) ς)
  (for/union : (℘ -ς) ([κ (σₖ@ σₖ αₖ)])
    (match-define (-κ ⟦k⟧ Γₑᵣ ⟪ℋ⟫ₑᵣ sₕ sₓs) κ)
    (define fargs (apply -?@ sₕ sₓs))
    ;(set! total (+ 1 total))
    (match A
      [(-W Vs sₐ)
       (define γ (-γ αₖ #f sₕ sₓs))
       (define Γₑᵣ**
         ; It's useful to check for feasibility of a strong path-condition
         ; before forgetting and keeping the path-condition address
         ; as an approximation
         ; TODO generalize
         (let-values ([(xs m)
                       (match αₖ
                         [(-ℬ xs _ _)
                          (define bounds (formals->names xs))
                          (define m
                            (match xs
                              [(? list? xs)
                               (for/hash : Subst ([x xs] [sₓ sₓs] #:when sₓ)
                                 (values (-x x) sₓ))]
                              [(-varargs xs x)
                               (define-values (args-init args-rest) (split-at sₓs (length xs)))
                               (define m-init
                                 (for/hash : Subst ([x xs] [arg args-init] #:when arg)
                                   (values (-x x) arg)))
                               (define s-rst (-?list args-rest))
                               (if s-rst (hash-set m-init (-x x) s-rst) m-init)]))
                          (values bounds m)]
                         [(-ℳ x _ _ _ _)
                          (define sₓ (car sₓs))
                          (values {seteq x} (if sₓ (hash-set m∅ (-x x) sₓ) m∅))]
                         [(-ℱ x _ _ _ _)
                          (define sₓ (car sₓs))
                          (values {seteq x} (if sₓ (hash-set m∅ (-x x) sₓ) m∅))])])
           (define φ-ans
             (match Vs
               [(list V)
                (match V
                  [(? -v? v)
                   (-?@ 'equal? (apply -?@ sₕ sₓs) v)]
                  [(or (? -Clo?) (? -Ar?) (? -o?))
                   (-?@ 'procedure? (apply -?@ sₕ sₓs))]
                  [_ #f])]
               [_ #f]))
           (define φs-path
             (for/fold ([φs-path : (℘ -e) ∅]) ([φ (-Γ-facts Γₑₑ)])
               (cond
                 [(⊆ (fv φ) xs) (set-add φs-path (e/map m φ))]
                 [else φs-path])))
           (apply Γ+ Γₑᵣ φ-ans (set->list φs-path))))
       (cond
         [(plausible-return? M Γₑᵣ** γ Γₑₑ)
          (define sₐ*
            (and sₐ
                 (match fargs ; HACK
                   [(-@ 'fc (list x) _)
                    (match Vs
                      [(list (-b #f)) -ff]
                      [(list (-b #t) _) (-?@ 'values -tt x)])]
                   [_ fargs])))
          (⟦k⟧ (-W Vs sₐ*) $∅ (-Γ-plus-γ Γₑᵣ γ) ⟪ℋ⟫ₑᵣ Σ)]
         [else ∅])]
      [(? -blm? blm) ; TODO: faster if had next `αₖ` here 
       (match-define (-blm l+ lo _ _) blm)
       (case l+
         [(havoc † Λ) ∅]
         [else
          (define γ (-γ αₖ (cons l+ lo) sₕ sₓs))
          (cond
            [(plausible-return? M Γₑᵣ γ Γₑₑ)
             (⟦k⟧ blm $∅ (-Γ-plus-γ Γₑᵣ γ) ⟪ℋ⟫ₑᵣ Σ)]
            [else ∅])])])))

(module+ test
  ((inst profile-thunk Void)
   (λ ()
     (printf "profiling execution of `slatex`~n")
     (havoc-file "../test/programs/safe/big/slatex.rkt")
     (void))))
