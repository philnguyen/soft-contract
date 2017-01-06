#lang typed/racket/base

(provide app mon flat-chk
         ap∷ let∷ if∷ and∷ or∷ bgn∷ bgn0.v∷ bgn0.e∷ rst-Γ∷
         mon.c∷ mon.v∷
         make-memoized-⟦k⟧
         mk-mon-⟦e⟧ mk-rt-⟦e⟧ mk-app-⟦e⟧)

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "../../primitives/main.rkt"
         "../../externals/def-ext-runtime.rkt"
         "utils.rkt"
         "base.rkt"
         racket/set
         racket/match
         (only-in racket/list split-at))

(: app : -l -$ -ℒ -W¹ (Listof -W¹) -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (app l $ ℒ Wₕ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)
  
  (match-define (-Σ σ σₖ M) Σ)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ
    (let ([sₕ* (match Vₕ
                 [(? -o? o) o]
                 [_ sₕ])])
      (apply -?@ sₕ* sₓs)))

  (: blm-arity ([Arity Natural] [#:name -s] . ->* . -blm))
  (define (blm-arity required provided #:name [f sₕ])
    ;; HACK for error message. Probably no need to fix
    (define msg : Symbol
      (cond
        [f (format-symbol "~a requires ~a arguments" (format "~a" (show-e f)) required)]
        [else (format-symbol "require ~a arguments" required)]))
    (-blm l 'Λ (list msg) Vₓs))

  (define-syntax-rule (with-guarded-arity a* e ...)
    (let ([n (length Wₓs)]
          [a a*])
      (cond
        [(arity-includes? a n) e ...]
        [else (⟦k⟧ (blm-arity a n) $ Γ ⟪ℋ⟫ Σ)])))

  (: make-arg-list! : Arity (Listof -W¹) → (℘ (U (Listof -W¹) -blm)))
  (define (make-arg-list! a Ws)
    (match a
      [(? exact-nonnegative-integer? n)
       (error 'make-arg-list! "TODO: exact arity ~a" n)]
      [(arity-at-least n)
       (error 'make-arg-list! "TODO: arity-at-least ~a" n)]
      [(? list?)
       (error 'make-arg-list! "TODO: case-lambda")]))

  (: app-prim-or-ext : Symbol → (℘ -ς))
  (define (app-prim-or-ext o)
    (cond
      [(get-prim o) =>
       (λ ([⟦o⟧ : -⟦o⟧])
         (match-define (-ℒ _ ℓ) ℒ)
         (for/union : (℘ -ς) ([ΓA (in-set (⟦o⟧ ⟪ℋ⟫ ℓ l Σ Γ Wₓs))])
           (match-define (-ΓA Γ A) ΓA)
           (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))]
      [(get-ext o) =>
       (λ ([⟦f⟧ : -⟦f⟧])
         (⟦f⟧ l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧))]
      [else (error 'app "don't know how to apply `~a`" o)]))

  (define (app-clo [xs : -formals] [⟦e⟧ : -⟦e⟧] [ρₕ : -ρ] [Γₕ : -Γ])

    (define plausible? ; conserivative `plausible?` to filter out some
      (cond [sₕ
             (for/and : Boolean ([γ (in-list (-Γ-tails Γ))])
               (match-define (-γ αₖ _ sₕ* _) γ)
               (cond [(equal? sₕ sₕ*)
                      (and (-ℬ? αₖ) (equal? (-ℬ-exp αₖ) ⟦e⟧))]
                     [else #t]))]
            [else #t]))

    (cond
      [plausible?
       (define ℯ (-edge ⟦e⟧ ℒ))
       ;; Extended call history
       (define ⟪ℋ⟫* (⟪ℋ⟫+ ⟪ℋ⟫ ℯ))
       ;; Context for allocating the value address
       (define ⟪ℋ⟫₀ (if (eq? ⟪ℋ⟫ ⟪ℋ⟫*) (⟪ℋ⟫@ ⟪ℋ⟫* ⟦e⟧) ⟪ℋ⟫*))
       ;; Call history for context jumped to
       (define ⟪ℋ⟫ₑₑ ⟪ℋ⟫₀ #;(if (eq? ⟪ℋ⟫* ⟪ℋ⟫) ⟪ℋ⟫₀ ⟪ℋ⟫*))
       ;; Target's environment
       (define ρ* : -ρ
         (match xs
           [(? list? xs)
            (alloc-init-args! σ Γ ρₕ ⟪ℋ⟫₀ xs Wₓs)]
           [(-varargs zs z)
            (define-values (Ws₀ Wsᵣ) (split-at Wₓs (length zs)))
            (define ρ₀ (alloc-init-args! σ Γ ρₕ ⟪ℋ⟫₀ zs Ws₀))
            (define Vᵣ (alloc-rest-args! σ Γ ⟪ℋ⟫₀ ℒ Wsᵣ))
            (define αᵣ (-α->-⟪α⟫ (-α.x z ⟪ℋ⟫₀)))
            (σ⊕! σ αᵣ Vᵣ)
            (ρ+ ρ₀ z αᵣ)]))

       (define αₖ (-ℬ xs ⟦e⟧ ρ*))
       (define κ (-κ (make-memoized-⟦k⟧ ⟦k⟧) Γ ⟪ℋ⟫ sₕ sₓs))
       (σₖ⊔! σₖ αₖ κ)
       {set (-ς↑ αₖ Γₕ ⟪ℋ⟫ₑₑ)}]
      [else ∅]))

  (define (app-And/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
    (define ⟦rhs⟧ (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W₂) (list (mk-rt-⟦e⟧ (car Wₓs)))))
    (app l $ ℒ W₁ Wₓs Γ ⟪ℋ⟫ Σ (and∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))

  (define (app-Or/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
    (define ⟦rhs⟧ (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W₂) (list (mk-rt-⟦e⟧ (car Wₓs)))))
    (app l $ ℒ W₁ Wₓs Γ ⟪ℋ⟫ Σ (or∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))
  
  (define (app-Not/C [Wᵤ : -W¹]) : (℘ -ς)
    (app l $ ℒ Wᵤ Wₓs Γ ⟪ℋ⟫ Σ (neg∷ l ⟦k⟧)))

  (define (app-St/C [𝒾 : -𝒾] [W-Cs : (Listof -W¹)]) : (℘ -ς)
    ;; TODO fix ℓ
    (match-define (list Wₓ) Wₓs)
    (match-define (-W¹ Vₓ _) Wₓ)
    (match Vₓ
      [(or (-St (== 𝒾) _) (-St* (== 𝒾) _ _ _))
       (define ⟦chk-field⟧s : (Listof -⟦e⟧)
         (for/list ([W-C (in-list W-Cs)]
                    [i (in-naturals)] #:when (index? i))
           (define Ac (let ([ac (-st-ac 𝒾 i)]) (-W¹ ac ac)))
           (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W-C)
                       (list (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ Ac) (list (mk-rt-⟦e⟧ Wₓ)))))))
       (define P (let ([p (-st-p 𝒾)]) (-W¹ p p)))
       (app l $ ℒ P (list Wₓ) Γ ⟪ℋ⟫ Σ (and∷ l ⟦chk-field⟧s ⊥ρ ⟦k⟧))]
      [_
       (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)]))

  (define (app-Ar [C : -V] [c : -s] [Vᵤ : -V] [l³ : -l³]) : (℘ -ς)
    (match-define (-l³ l+ l- lo) l³)
    (define Wᵤ (-W¹ Vᵤ sₕ)) ; inner function
    (match-define (-=> αℓs βℓ _) C)
    (match-define (cons β ℓᵣ) βℓ)
    (define-values (cs d) (-->-split c (length αℓs)))
    (match-define (-Σ σ _ _) Σ)
    (cond
      ;; FIXME: prevent this
      [(equal? Vᵤ Vₕ)
       (log-warning "TODO: generalize to handle cycle properly")
       ∅]
      [else
       (match cs
         ['() ; no arg
          (for/union : (℘ -ς) ([D (σ@ σ β)])
            (app lo $ ℒ Wᵤ '() Γ ⟪ℋ⟫ Σ
                 (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵣ) (-W¹ D d) ⟦k⟧)))]
         [(? pair?)
          (define-values (αs ℓs) ((inst unzip -⟪α⟫ -ℓ) αℓs))
          (define l³* (-l³ l- l+ lo))
          (for/union : (℘ -ς) ([Cs (in-set (σ@/list σ αs))])
            (match-define (cons ⟦mon-x⟧ ⟦mon-x⟧s)
              (for/list : (Listof -⟦e⟧) ([C Cs] [c cs] [Wₓ Wₓs] [ℓₐ : -ℓ ℓs])
                ;(printf "mon-arg: ~a ~a ~a~n" (+ℓ/ℓ² ℓ ℓₐ) (show-W¹ (-W¹ C c)) (show-W¹ Wₓ))
                (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₐ) (mk-rt-⟦e⟧ (-W¹ C c)) (mk-rt-⟦e⟧ Wₓ))))
            (for/union : (℘ -ς) ([D (in-set (σ@ σ β))])
              (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
               (ap∷ (list Wᵤ) ⟦mon-x⟧s ⊥ρ lo ℒ
                    (mon.c∷ l³ (ℒ-with-mon ℒ ℓᵣ) (-W¹ D d) ⟦k⟧)))))])]))

  (define (app-Indy [C : -V] [c : -s] [Vᵤ : -V] [l³ : -l³]) : (℘ -ς)
    (match-define (-l³ l+ l- lo) l³)
    (define l³* (-l³ l- l+ lo))
    (define Wᵤ (-W¹ Vᵤ sₕ)) ; inner function
    (match-define (-=>i αℓs (list Mk-D mk-d ℓᵣ) _) C)
    (match-define (-Clo xs ⟦d⟧ ρᵣ _) Mk-D)
    (define W-rng (-W¹ Mk-D mk-d))
    ;(match-define (cons γ ℓᵣ) γℓ)
    (define-values (αs ℓs) ((inst unzip -⟪α⟫ -ℓ) αℓs))
    (define cs
      (let-values ([(cs _) (-->i-split c (length αℓs))])
        cs))

    ;; FIXME tmp. copy n paste. Remove duplication
    (match mk-d
      [(-λ (? list? xs) d)
       (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
         (define ⟦mon-x⟧s : (Listof -⟦e⟧)
           (for/list ([C Cs] [c cs] [Wₓ Wₓs] [ℓₐ : -ℓ ℓs])
             (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₐ) (mk-rt-⟦e⟧ (-W¹ C c)) (mk-rt-⟦e⟧ Wₓ))))
         (define ⟦x⟧s : (Listof -⟦e⟧) (for/list ([x xs]) (↓ₓ 'Λ x)))
         (match* (xs ⟦x⟧s ⟦mon-x⟧s)
           [('() '() '())
            (define ⟦ap⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ) '()))
            (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦d⟧ ⟦ap⟧))
            (⟦mon⟧ ρᵣ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
           [((cons x xs*) (cons ⟦x⟧ ⟦x⟧s*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
            (define ⟦app⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ) ⟦x⟧s))
            (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦d⟧ ⟦app⟧))
            (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
             (let∷ lo
                   (list x)
                   (for/list ([xᵢ xs*] [⟦mon⟧ᵢ ⟦mon-x⟧s*])
                     (cons (list xᵢ) ⟦mon⟧ᵢ))
                   '()
                   ⟦mon⟧
                   ρᵣ
                    ⟦k⟧))]))]
      [_
       (match xs
         [(? list? xs)
          (define ⟦x⟧s : (Listof -⟦e⟧) (for/list ([x xs]) (↓ₓ lo x)))
          (for/union : (℘ -ς) ([Cs (σ@/list σ αs)] [ℓₐ : -ℓ ℓs])
            (define ⟦mon-x⟧s : (Listof -⟦e⟧)
              (for/list ([C Cs] [c cs] [Wₓ Wₓs])
                (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓₐ) (mk-rt-⟦e⟧ (-W¹ C c)) (mk-rt-⟦e⟧ Wₓ))))
            (match* (xs ⟦x⟧s ⟦mon-x⟧s)
              [('() '() '())
               (define ⟦app⟧  (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ   ) '()))
               (define ⟦mk-d⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ W-rng) '()))
               (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦mk-d⟧ ⟦app⟧))
               (⟦mon⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
              [((cons x xs*) (cons ⟦x⟧ ⟦x⟧s*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
               (define ⟦mon-y⟧
                 (let ([⟦mk-d⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ W-rng) ⟦x⟧s)]
                       [⟦app⟧  (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ Wᵤ   ) ⟦x⟧s)])
                   (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵣ) ⟦mk-d⟧ ⟦app⟧)))
               (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
                (let∷ lo
                      (list x)
                      (for/list ([xᵢ xs*] [⟦mon⟧ᵢ ⟦mon-x⟧s*])
                        (cons (list xᵢ) ⟦mon⟧ᵢ))
                      '()
                      ⟦mon-y⟧
                      ⊥ρ
                       ⟦k⟧))]))]
         [(-varargs zs z)
          (error 'app-Indy "Apply variable arity arrow")])]))

  (define (app-Case [C : -V] [c : -s] [Vᵤ : -V] [l³ : -l³]) : (℘ -ς)
    (error 'app-Case "TODO"))

  (match Vₕ
    ;; In the presence of struct contracts, field accessing is not an atomic operation
    ;; because structs can be contract-wrapped arbitrarily deeply,
    ;; plus contracts can be arbitrary code.
    ;; This means field accessing cannot be implemented in `δ`
    [(-st-p  𝒾) ((app-st-p 𝒾) l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-st-mk 𝒾) ((app-st-mk 𝒾) l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-st-ac  𝒾 i) ((app-st-ac  𝒾 i) l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(-st-mut 𝒾 i) ((app-st-mut 𝒾 i) l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    ['apply (app-apply l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]

    ;; Regular stuff
    [(? symbol? o) (app-prim-or-ext o)]
    [(-Clo xs ⟦e⟧ ρₕ Γₕ)
     (with-guarded-arity (formals-arity xs)
       (app-clo xs ⟦e⟧ ρₕ Γₕ))]
    [(-Case-Clo clauses ρ Γ)
     (define n (length Wₓs))
     (define clause
       (for/or : (Option (Pairof (Listof Symbol) -⟦e⟧)) ([clause clauses])
         (match-define (cons xs _) clause)
         (and (equal? n (length xs)) clause)))
     (cond
       [clause
        (match-define (cons xs ⟦e⟧) clause)
        (app-clo xs ⟦e⟧ ρ Γ)]
       [else
        (define a (assert (V-arity Vₕ)))
        (⟦k⟧ (blm-arity a n) $ Γ ⟪ℋ⟫ Σ)])]
    [(-Ar C α l³)
     (with-guarded-arity (guard-arity C)
       (define-values (c _) (-ar-split sₕ))
       (cond
         [(-=>? C)  (for/union : (℘ -ς) ([Vᵤ (σ@ σ α)]) (app-Ar   C c Vᵤ l³))]
         [(-=>i? C) (for/union : (℘ -ς) ([Vᵤ (σ@ σ α)]) (app-Indy C c Vᵤ l³))]
         [else      (for/union : (℘ -ς) ([Vᵤ (σ@ σ α)]) (app-Case C c Vᵤ l³))]))]
    [(-And/C #t (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (with-guarded-arity 1
       (define-values (c₁ c₂)
         (match-let ([(list s₁ s₂) (-app-split sₕ 'and/c 2)])
           (values (or s₁ (⟪α⟫->s α₁))
                   (or s₂ (⟪α⟫->s α₂)))))
       (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
         (app-And/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
    [(-Or/C #t (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (with-guarded-arity 1
       (define-values (c₁ c₂)
         (match-let ([(list s₁ s₂) (-app-split sₕ 'or/c 2)])
           (values (or s₁ (⟪α⟫->s α₁))
                   (or s₂ (⟪α⟫->s α₂)))))
       (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
         (app-Or/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
    [(-Not/C (cons α ℓ*))
     (with-guarded-arity 1
       (define c*
         (match-let ([(list s) (-app-split sₕ 'not/c 1)])
           (or s (⟪α⟫->s α))))
       (for/union : (℘ -ς) ([C* (σ@ σ α)])
         (app-Not/C (-W¹ C* c*))))]
    [(-St/C #t s αℓs)
     (with-guarded-arity 1
       (define-values (αs ℓs) ((inst unzip -⟪α⟫ -ℓ) αℓs))
       (define cs : (Listof -s)
         (for/list ([s (-struct/c-split sₕ s)]
                    [α : -⟪α⟫ αs])
           (or s (⟪α⟫->s α))))
       (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
         (app-St/C s (map -W¹ Cs cs))))]
    [(-● _)
     (case (MΓ⊢oW M σ Γ 'procedure? Wₕ)
       [(✓ ?) ((app-opq sₕ) l $ ℒ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
       [(✗) (⟦k⟧ (-blm l 'Λ (list 'procedure?) (list Vₕ)) $ Γ ⟪ℋ⟫ Σ)])]
    [_
     (define blm (-blm l 'Λ (list 'procedure?) (list Vₕ)))
     (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Applications
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -⟦f⟧ (-l -$ -ℒ (Listof -W¹) -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))

(: app-st-p : -𝒾 → -⟦f⟧)
(define (app-st-p 𝒾)
  (define st-p (-st-p 𝒾))
  (λ (l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match Ws
      [(list (and W (-W¹ _ s)))
       (match-define (-Σ σ _ M) Σ)
       (define sₐ (-?@ st-p s))
       (define A
         (case (MΓ⊢oW M σ Γ st-p W)
           [(✓) -True/Vs]
           [(✗) -False/Vs]
           [(?) -Bool/Vs]))
       (⟦k⟧ (-W A sₐ) $ Γ ⟪ℋ⟫ Σ)]
      [_
       (define blm (blm-arity l (show-o st-p) 1 (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(: app-st-mk : -𝒾 → -⟦f⟧)
(define (app-st-mk 𝒾)
  (define st-mk (-st-mk 𝒾))
  (define n (get-struct-arity 𝒾))
  (λ (l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (cond
      [(= n (length Ws))
       (match-define (-Σ σ _ M) Σ)
       (define sₐ (apply -?@ st-mk (map -W¹-s Ws)))
       (define αs : (Listof -⟪α⟫)
         (for/list ([i : Index n])
           (-α->-⟪α⟫ (-α.fld 𝒾 ℒ ⟪ℋ⟫ i))))
       (for ([α : -⟪α⟫ αs] [W (in-list Ws)])
         (match-define (-W¹ V s) W)
         (define V* (V+ σ V (predicates-of Γ s)))
         (σ⊕! σ α V*))
       (define V (-St 𝒾 αs))
       (⟦k⟧ (-W (list V) sₐ) $ Γ ⟪ℋ⟫ Σ)]
      [else
       (define blm (blm-arity l (show-o st-mk) n (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(: app-st-ac : -𝒾 Index → -⟦f⟧)
(define (app-st-ac 𝒾 i)
  (define ac (-st-ac 𝒾 i))
  (define p  (-st-p 𝒾))
  (define n (get-struct-arity 𝒾))
  (define mutable-field? (struct-mutable? 𝒾 i))
  
  (: ⟦ac⟧ : -⟦f⟧)
  (define (⟦ac⟧ l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match Ws
      [(list (and W (-W¹ V s)))
       (define (blm) (-blm l (show-o ac) (list p) (list V)))
       (match-define (-Σ σ _ M) Σ)
       (define sₐ (-?@ ac s))
       (match V
         [(-St (== 𝒾) αs)
          (define α (list-ref αs i))
          (cond
            [(and (not mutable-field?) ($@ $ sₐ)) =>
             (λ ([V : -V])
               (cond [(plausible-V-s? (-Γ-facts Γ) V sₐ)
                      (define $* ($+ $ sₐ V))
                      (⟦k⟧ (-W (list V) sₐ) $* Γ ⟪ℋ⟫ Σ)]
                     [else ∅]))]
            [else
             (define Vs (σ@ σ α))
             (for/union : (℘ -ς) ([V Vs])
                (cond [(plausible-V-s? (-Γ-facts Γ) V sₐ)
                       (define $* (if mutable-field? $ ($+ $ sₐ V)))
                       (⟦k⟧ (-W (list V) sₐ) $* Γ ⟪ℋ⟫ Σ)]
                      [else ∅]))])]
         [(-St* (== 𝒾) αs α l³)
          (match-define (-l³ _ _ lₒ) l³)
          (define Ac (-W¹ ac ac))
          (cond
            ;; field is wrapped
            [(list-ref αs i) =>
             (λ ([αᵢ : -⟪α⟫])
               (define Cᵢs (σ@ σ αᵢ))
               (define Vs  (σ@ σ α))
               (define cᵢ (⟪α⟫->s αᵢ))
               (for*/union : (℘ -ς) ([Cᵢ (in-set Cᵢs)] [V* (in-set Vs)])
                 (⟦ac⟧ lₒ $ ℒ (list (-W¹ V* s)) Γ ⟪ℋ⟫ Σ
                   (mon.c∷ l³ ℒ (-W¹ Cᵢ cᵢ) ⟦k⟧))))]
            ;; field is unwrapped because it's immutable
            [else
             ;; TODO: could this loop forever due to cycle?
             (for/union : (℘ -ς) ([V* (in-set (σ@ σ α))])
                (⟦ac⟧ lₒ $ ℒ (list (-W¹ V* s)) Γ ⟪ℋ⟫ Σ ⟦k⟧))])]
         [(-● ps)
          (with-Γ+/- ([(Γₒₖ Γₑᵣ) (MΓ+/-oW M σ Γ p W)])
            #:true  (⟦k⟧ (-W (if (and (equal? 𝒾 -𝒾-cons) (equal? i 1) (∋ ps 'list?))
                                 (list (-● {set 'list?}))
                                 -●/Vs)
                             sₐ)
                     $ Γₒₖ ⟪ℋ⟫ Σ)
            #:false (⟦k⟧ (blm) $ Γₑᵣ ⟪ℋ⟫ Σ))]
         [_ (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)])]
      [_
       (define blm (blm-arity l (show-o ac) 1 (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
  ⟦ac⟧)

(: app-st-mut : -𝒾 Index → -⟦f⟧)
(define (app-st-mut 𝒾 i)
  (define mut (-st-mut 𝒾 i))
  (define p (-st-p 𝒾))
  
  (: ⟦mut⟧ : -⟦f⟧)
  (define (⟦mut⟧ l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match Ws
      [(list Wₛ Wᵥ)
       (match-define (-Σ σ _ M) Σ)
       (match-define (-W¹ Vₛ sₛ) Wₛ)
       (match-define (-W¹ Vᵥ _ ) Wᵥ)
       (define (blm) (-blm l (show-o mut) (list p) (list Vₛ)))
       
       (match Vₛ
         [(-St (== 𝒾) αs)
          (define α (list-ref αs i))
          (σ⊕! σ α Vᵥ #:mutating? #t)
          (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)]
         [(-St* (== 𝒾) γs α l³)
          (match-define (-l³ l+ l- lo) l³)
          (define l³* (-l³ l- l+ lo))
          (match-define (? -α? γ) (list-ref γs i))
          (define c (⟪α⟫->s γ))
          (define Mut (-W¹ mut mut))
          (for*/union : (℘ -ς) ([C (σ@ σ γ)] [Vₛ* (σ@ σ α)])
                      (define W-c (-W¹ C c))
                      (define Wₛ* (-W¹ Vₛ* sₛ))
                      (mon l³* $ ℒ W-c Wᵥ Γ ⟪ℋ⟫ Σ
                           (ap∷ (list Wₛ Mut) '() ⊥ρ lo ℒ ⟦k⟧)))]
         [(-● _)
          (define ⟦ok⟧
            (let ([⟦hv⟧ (mk-app-⟦e⟧ 'havoc ℒ
                                    (mk-rt-⟦e⟧ (-W¹ -●/V #f))
                                    (list (mk-rt-⟦e⟧ Wᵥ)))])
              (mk-app-⟦e⟧ 'havoc ℒ (mk-rt-⟦e⟧ (-W¹ 'void 'void)) (list ⟦hv⟧))))
          (define ⟦er⟧ (mk-rt-⟦e⟧ (blm)))
          (app 'Λ $ ℒ (-W¹ p p) (list Wₛ) Γ ⟪ℋ⟫ Σ (if∷ l ⟦ok⟧ ⟦er⟧ ⊥ρ ⟦k⟧))]
         [_ (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)])]
      [_
       (define blm (blm-arity l (show-o mut) 2 (map -W¹-V Ws)))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
  ⟦mut⟧)

(: app-apply : -⟦f⟧)
(define (app-apply l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ M) Σ)
  (match-define (cons W₀ Wᵢs) Ws)
  ;; special case for `slatex`
  (match* (W₀ Wᵢs)
    [((-W¹ (-Clo (-varargs (list x) xᵣ) ⟦e⟧ ρ Γ) sₕ) (list W₁ W₂ Wᵣ))
     (match-define (-W¹ V₂ s₂) W₂)
     (match-define (-W¹ Vᵣ sᵣ) Wᵣ)
     (define Wₗ
       (let ([sₗ (-?@ -cons s₂ sᵣ)]
             [αₕ (-α->-⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ 0))]
             [αₜ (-α->-⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ 1))])
         (define Vₗ (-Cons αₕ αₜ))
         (σ⊕*! σ [αₕ ↦ V₂] [αₜ ↦ Vᵣ])
         (-W¹ Vₗ sₗ)))
     (app l $ ℒ (-W¹ (-Clo (list x xᵣ) ⟦e⟧ ρ Γ) sₕ) (list W₁ Wₗ) Γ ⟪ℋ⟫ Σ ⟦k⟧)]
    [(_ _)
     (error 'app-apply "TODO: ~a ~a" (show-W¹ W₀) (map show-W¹ Wᵢs))]))

(: app-opq : -s → -⟦f⟧)
(define ((app-opq sₕ) l $ ℒ Ws Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ σₖ _) Σ)
  (define sₐ (apply -?@ sₕ (map -W¹-s Ws)))
  (define αₖ (-ℋ𝒱* ℒ (for/set: : (℘ -V) ([W (in-list Ws)]) (-W¹-V W))))
  (define κ (-κ (bgn0.e∷ (-W -●/Vs sₐ) '() ⊥ρ ⟦k⟧) Γ ⟪ℋ⟫ 'void '()))
  (σₖ⊔! σₖ αₖ κ)
  {set (-ς↑ αₖ Γ ⟪ℋ⟫)})

(: alloc-init-args! : -σ -Γ -ρ -⟪ℋ⟫ (Listof Symbol) (Listof -W¹) → -ρ)
(define (alloc-init-args! σ Γ ρ ⟪ℋ⟫ xs Ws)
  (define ρ₀ (ρ+ ρ -x-dummy (-α->-⟪α⟫ (-α.x -x-dummy ⟪ℋ⟫))))
  (for/fold ([ρ : -ρ ρ₀]) ([x xs] [Wₓ Ws])
    (match-define (-W¹ Vₓ sₓ) Wₓ)
    (define α (-α->-⟪α⟫ (-α.x x ⟪ℋ⟫)))
    (define Vₓ*
      ;; Refine arguments by type-like contracts before proceeding
      ;; This could save lots of spurious errors to eliminate later
      (V+ σ Vₓ (predicates-of Γ sₓ)))
    (σ⊕! σ α Vₓ*)
    
    ;; Debug for `slatex`
    #;(when (and (member x '(raw-filename s₃ filename filename₁))
               (match? Wₓ (-W¹ (? -●?) _)))
      (printf "binding ~a as ~a~n~n" x (show-W¹ Wₓ)))

    (ρ+ ρ x α)))

(: alloc-rest-args! : -σ -Γ -⟪ℋ⟫ -ℒ (Listof -W¹) → -V)
(define (alloc-rest-args! σ Γ ⟪ℋ⟫ ℒ Ws)

  (: precise-alloc! ([(Listof -W¹)] [Natural] . ->* . -V))
  ;; Allocate vararg list precisely, preserving length
  (define (precise-alloc! Ws [i 0])
    (match Ws
      [(list) -null]
      [(cons (-W¹ Vₕ _) Ws*)
       (define αₕ (-α->-⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ i)))
       (define αₜ (-α->-⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ i)))
       (σ⊕*! σ [αₕ ↦ Vₕ]
               [αₜ ↦ (precise-alloc! Ws* (+ 1 i))])
       (-Cons αₕ αₜ)]))
  
  ;; Allocate length up to 2 precisely to let `splay` to go through
  ;; This is because `match-lambda*` expands to varargs with specific
  ;; expectation of arities
  (match Ws
    [(or (list) (list _) (list _ _))
     (precise-alloc! Ws)]
    [(? pair?)
     (define αₕ (-α->-⟪α⟫ (-α.var-car ℒ ⟪ℋ⟫ #f)))
     (define αₜ (-α->-⟪α⟫ (-α.var-cdr ℒ ⟪ℋ⟫ #f)))
     (define Vₜ (-Cons αₕ αₜ))
     ;; Allocate spine for var-arg lists
     (σ⊕*! σ [αₜ ↦ Vₜ] [αₜ ↦ -null])
     ;; Allocate elements in var-arg lists
     (for ([W Ws])
       (match-define (-W¹ Vₕ sₕ) W)
       (σ⊕! σ αₕ (V+ σ Vₕ (predicates-of Γ sₕ))))
     Vₜ]))

(: mon : -l³ -$ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (mon l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ C _) W-C)
  (define mon*
    (cond
      [(-=>_? C) mon-=>_]
      [(-St/C? C) mon-struct/c]
      [(-x/C? C) mon-x/c]
      [(-And/C? C) mon-and/c]
      [(-Or/C? C) mon-or/c]
      [(-Not/C? C) mon-not/c]
      [(-Vectorof? C) mon-vectorof]
      [(-Vector/C? C) mon-vector/c]
      [else mon-flat/c]))
  (mon* l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Application
(define/memo (ap∷ [Ws : (Listof -W¹)]
                  [⟦e⟧s : (Listof -⟦e⟧)]
                  [ρ : -ρ]
                  [l : -l]
                  [ℒ : -ℒ]
                  [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Ws ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define Ws* (cons (-W¹ V s) Ws))
       (match ⟦e⟧s
         ['()
          (match-define (cons Wₕ Wₓs) (reverse Ws*))
          (app l $ ℒ Wₕ Wₓs Γ ⟪ℋ⟫ Σ ⟦k⟧)]
         [(cons ⟦e⟧ ⟦e⟧s*)
          (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ Ws* ⟦e⟧s* ρ l ℒ ⟦k⟧))])]
      [_
       (define blm
         (-blm l 'Λ (list '1-value) (list (format-symbol "~a values" (length Vs)))))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (mon.c∷ [l³ : -l³]
                     [ℒ : -ℒ]
                     [C : (U (Pairof -⟦e⟧ -ρ) -W¹)]
                     [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match-define (-l³ _ _ lo) l³)
  (define root (if (pair? C) (cdr C) C))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (define W-V (-W¹ V s))
       (cond [(-W¹? C) (mon l³ $ ℒ C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
             [else
              (match-define (cons ⟦c⟧ ρ) C)
              (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ l³ ℒ W-V ⟦k⟧))])]
      [else
       (define blm (-blm lo 'Λ '(|1 value|) Vs))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (mon.v∷ [l³ : -l³]
                     [ℒ : -ℒ]
                     [V : (U (Pairof -⟦e⟧ -ρ) -W¹)]
                     [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match-define (-l³ _ _ lo) l³)
  (define root (if (pair? V) (cdr V) V))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (root)
    (match-define (-W Vs s) A)
    (match Vs
      [(list C)
       (define W-C (-W¹ C s))
       (cond [(-W¹? V) (mon l³ $ ℒ W-C V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
             [else
              (match-define (cons ⟦v⟧ ρ) V)
              (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.c∷ l³ ℒ W-C ⟦k⟧))])]
      [else
       (define blm (-blm lo 'Λ '(|1 value|) Vs))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; let-values
(define/memo (let∷ [l : -l]
                   [xs : (Listof Symbol)]
                   [⟦bnd⟧s : (Listof (Pairof (Listof Symbol) -⟦e⟧))]
                   [bnd-Ws : (Listof (List Symbol -V -s))]
                   [⟦e⟧ : -⟦e⟧]
                   [ρ : -ρ]
                   [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (define n (length xs))
    
    (cond
      [(= n (length Vs))
       (define bnd-Ws*
         (for/fold ([acc : (Listof (List Symbol -V -s)) bnd-Ws])
                   ([x xs] [V Vs] [sₓ (split-values s n)])
           (cons (list x V sₓ) acc)))
       (match ⟦bnd⟧s
         ['()
          (match-define (-Σ σ _ _) Σ)
          (define-values (ρ* Γ*) ; with side effect widening store
            (for/fold ([ρ : -ρ ρ] [Γ : -Γ Γ])
                      ([bnd-W bnd-Ws*])
              (match-define (list (? symbol? x) (? -V? Vₓ) (? -s? sₓ)) bnd-W)
              (define α (-α->-⟪α⟫ (-α.x x ⟪ℋ⟫)))
              (σ⊕! σ α (V+ σ Vₓ (predicates-of Γ sₓ)))
              (values (ρ+ ρ x α) (-Γ-with-aliases Γ x sₓ))))
          (⟦e⟧ ρ* $ Γ* ⟪ℋ⟫ Σ ⟦k⟧)]
         [(cons (cons xs* ⟦e⟧*) ⟦bnd⟧s*)
          (⟦e⟧* ρ $ Γ ⟪ℋ⟫ Σ (let∷ l xs* ⟦bnd⟧s* bnd-Ws* ⟦e⟧ ρ ⟦k⟧))])]
      [else
       (define blm
         (-blm l 'let-values
               (list (format-symbol "requires ~a values" (length xs)))
               (list (format-symbol "provided ~a values" (length Vs)))))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;; begin
(define/memo (bgn∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (rst-Γ∷ Γ (make-memoized-⟦k⟧ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))))]))

;; begin0, waiting on first value
(define/memo (bgn0.v∷ [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (rst-Γ∷ Γ (bgn0.e∷ A ⟦e⟧s* ρ ⟦k⟧))))]))

;; begin0, already have first value
(define/memo (bgn0.e∷ [W : -W] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['()
     (with-error-handling (⟦k⟧ _ $ Γ ⟪ℋ⟫ Σ) #:roots (W)
       (⟦k⟧ W $ Γ ⟪ℋ⟫ Σ))]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (with-error-handling (⟦k⟧ _ $ Γ ⟪ℋ⟫ Σ) #:roots (W ρ)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (rst-Γ∷ Γ (bgn0.e∷ W ⟦e⟧s* ρ ⟦k⟧))))]))

;; clean-up path-condition
(define/memo (rst-Γ∷ [Γ : -Γ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ _ ⟪ℋ⟫ Σ) #:roots ()
    (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(:* mon-=>_ mon-struct/c mon-x/c mon-and/c mon-or/c mon-not/c mon-vectorof mon-vector/c mon-flat/c :
    -l³ -$ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))

(define (mon-=>_ l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ (? -=>_? grd) c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-Σ σ _ M) Σ)

  (define arity
    (let* ([a (guard-arity grd)]
           [b (-b a)])
      (-W¹ b b)))
  
  (define-values (Γ₁ Γ₂) (MΓ+/-oW M σ Γ 'procedure? W-V))
  (define-values (Γ₁₁ Γ₁₂)
    (if Γ₁
        (let ([A (V-arity V)]
              [a (-?@ 'procedure-arity v)])
          (define W-a (-W¹ (if A (-b A) -●/V) a))
          (MΓ+/-oW M σ Γ₁ 'arity-includes? W-a arity))
        (values #f #f)))
  #;(match-define (-ℒ _ ℓ) ℒ)
  (∪ (cond [Γ₁₁
            (define grd-ℓ
              (cond [(-=>? grd) (-=>-pos grd)]
                    [(-=>i? grd) (-=>i-pos grd)]
                    [else (error 'mon-=>_ "unexpected")]))
            (define α (-α->-⟪α⟫ (or (keep-if-const v) (-α.fn ℒ grd-ℓ ⟪ℋ⟫))))
            (define Ar (-Ar grd α l³))
            (σ⊕! σ α V)
            (define v* ; hack
              (match v
                [(-ar (== c) _) v]
                [_ (-?ar c v)]))
            (⟦k⟧ (-W (list Ar) v*) $ Γ₁₁ ⟪ℋ⟫ Σ)]
           [else ∅])
     (cond [Γ₁₂
            (define C #|HACK|#
              (match arity
                [(-W¹ (-b (? integer? n)) _)
                 (format-symbol "(arity-includes/c ~a)" n)]
                [(-W¹ (-b (arity-at-least n)) _)
                 (format-symbol "(arity-at-least/c ~a)" n)]))
            (⟦k⟧ (-blm l+ lo (list C) (list V)) $ Γ₁₂ ⟪ℋ⟫ Σ)]
           [else ∅])
     (cond [Γ₂ (⟦k⟧ (-blm l+ lo (list 'procedure?) (list V)) $ Γ₂ ⟪ℋ⟫ Σ)]
           [else ∅])))

(define (mon-struct/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-St/C flat? 𝒾 αℓs) C)
  (define-values (αs ℓs) ((inst unzip -⟪α⟫ -ℓ) αℓs))
  (define cs (-struct/c-split c 𝒾))
  (define p (-st-p 𝒾))
  (define K (let ([k (-st-mk 𝒾)]) (-W¹ k k)))
  (define all-immutable? (struct-all-immutable? 𝒾))

  (define ⟦field⟧s : (Listof -⟦e⟧)
    (for/list ([α (in-list αs)]
               [i (in-naturals)] #:when (index? i))
      (define ac (-st-ac 𝒾 i))
      (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ (-W¹ ac ac)) (list (mk-rt-⟦e⟧ (-W¹ V v))))))

  (match V ; FIXME code dup
    [(or (-St (== 𝒾) _) (-St* (== 𝒾) _ _ _))
     (cond
       [(null? ⟦field⟧s)
        (⟦k⟧ (-W (list V) v) $ Γ ⟪ℋ⟫ Σ)]
       [else
        (match-define (-ℒ _ ℓ) ℒ)
        (for/union : (℘ -ς) ([Cs (σ@/list (-Σ-σ Σ) αs)])
                   (define ⟦mon⟧s : (Listof -⟦e⟧)
                     (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s] [ℓᵢ : -ℓ ℓs])
                       (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
                   (define ⟦reconstr⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ K) ⟦mon⟧s))
                   (define ⟦k⟧*
                     (cond [all-immutable? ⟦k⟧]
                           [else
                            (define α (-α->-⟪α⟫ (-α.st 𝒾 ℓ ⟪ℋ⟫)))
                            (wrap-st∷ 𝒾 αs α l³ ⟦k⟧)]))
                   (⟦reconstr⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))])]
    [(-● _)
     (match-define (-ℒ _ ℓ) ℒ)
     (define ⟦chk⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ (-W¹ p p)) (list (mk-rt-⟦e⟧ W-V))))
     (define ⟦blm⟧ (mk-rt-⟦e⟧ (-blm l+ lo (list p) (list V))))
     (cond
       [(null? ⟦field⟧s)
        (define ⟦rt⟧ (mk-rt-⟦e⟧ W-V))
        (⟦chk⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (if∷ lo ⟦rt⟧ ⟦blm⟧ ⊥ρ ⟦k⟧))]
       [else
        (for/union : (℘ -ς) ([Cs (σ@/list (-Σ-σ Σ) αs)])
          (define ⟦mon⟧s : (Listof -⟦e⟧)
            (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s] [ℓᵢ : -ℓ ℓs])
              (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
          (define ⟦reconstr⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ K) ⟦mon⟧s))
          (define ⟦k⟧*
            (cond
              [all-immutable? ⟦k⟧]
              [else
               (define α (-α->-⟪α⟫ (-α.st 𝒾 ℓ ⟪ℋ⟫)))
               (wrap-st∷ 𝒾 αs α l³ ⟦k⟧)]))
          (⟦chk⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
           (if∷ lo ⟦reconstr⟧ ⟦blm⟧ ⊥ρ ⟦k⟧*)))])]
    [_ (⟦k⟧ (-blm l+ lo (list C) (list V)) $ Γ ⟪ℋ⟫ Σ)]))

(define (mon-x/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match-define (-x/C ⟪α⟫) C)
  (define x (match-let ([(-α.x/c x*) (-⟪α⟫->-α ⟪α⟫)])
              (+x!/memo 'mon x*)))
  (define 𝐱 (-x x))
  (match-define (-Σ σ σₖ _) Σ)
  (for/set: : (℘ -ς) ([C* (σ@ σ ⟪α⟫)])
    (define αₖ
      (let ([W-C* (-W¹ C* c)]
            [W-V* (-W¹ V 𝐱)])
        (-ℳ x l³ ℒ W-C* W-V*)))
    (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ #|FIXME hack|# 'values (list v)))
    (σₖ⊔! σₖ αₖ κ)
    (-ς↑ αₖ ⊤Γ #;Γ* ⟪ℋ⟫)))

(define (mon-and/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (match-define (-W¹ (-And/C _ (cons α₁ ℓ₁) (cons α₂ ℓ₂)) c) W-C)
  (match-define (list c₁ c₂) (-app-split c 'and/c 2))
  (for/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
    (mon l³ $ (ℒ-with-mon ℒ ℓ₁) (-W¹ C₁ c₁) W-V Γ ⟪ℋ⟫ Σ 
         (mon.c∷ l³ (ℒ-with-mon ℒ ℓ₂) (-W¹ C₂ c₂) ⟦k⟧))))

(define (mon-or/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ (-Or/C flat? (cons α₁ ℓ₁) (cons α₂ ℓ₂)) c) W-C)
  (define-values (c₁ c₂)
    (match-let ([(list s₁ s₂) (-app-split c 'or/c 2)])
      (values (or s₁ (⟪α⟫->s α₁))
              (or s₂ (⟪α⟫->s α₂)))))
  
  (: chk-or/c : -W¹ -ℓ -W¹ -ℓ → (℘ -ς))
  (define (chk-or/c W-fl ℓ-fl W-ho ℓ-ho)
    (flat-chk lo $ (ℒ-with-mon ℒ ℓ-fl) W-fl W-V Γ ⟪ℋ⟫ Σ
              (mon-or/c∷ l³ (ℒ-with-mon ℒ ℓ-ho) W-fl W-ho W-V ⟦k⟧)))

  (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
    (define W-C₁ (-W¹ C₁ c₁))
    (define W-C₂ (-W¹ C₂ c₂))
    (cond [(C-flat? C₁) (chk-or/c W-C₁ ℓ₁ W-C₂ ℓ₂)]
          [(C-flat? C₂) (chk-or/c W-C₂ ℓ₂ W-C₁ ℓ₁)]
          [else (error 'or/c "No more than 1 higher-order disjunct for now")])))

(define (mon-not/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ (and C (-Not/C (cons α ℓ*))) c) W-C)
  (match-define (-W¹ V _) W-V)
  (match-define (list c*) (-app-split c 'not/c 1))
  (define ⟦k⟧*
    (let ([⟦ok⟧ (mk-rt-⟦e⟧ W-V)]
          [⟦er⟧ (mk-rt-⟦e⟧ (-blm l+ lo (list C) (list V)))])
      (if∷ lo ⟦er⟧ ⟦ok⟧ ⊥ρ ⟦k⟧)))
  (for/union : (℘ -ς) ([C* (σ@ (-Σ-σ Σ) α)])
    (assert C* C-flat?)
    (define W-C* (-W¹ C* c*))
    (app lo $ (ℒ-with-mon ℒ ℓ*) W-C* (list W-V) Γ ⟪ℋ⟫ Σ ⟦k⟧*)))

(define (mon-vectorof l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ Vᵥ sᵥ) W-V)
  (match-define (-W¹ (-Vectorof (cons α ℓ*)) _) W-C)
  (define c (⟪α⟫->s α))
  (define ⟦rt⟧ (mk-rt-⟦e⟧ W-V))

  ;(printf "mon-vectorof ~a on ~a~n" (show-W¹ W-C) (show-W¹ W-V))
  
  (match Vᵥ
    [(-Vector αs)
     (define ⟦erase⟧ (mk-erase-⟦e⟧ αs))
     (define ⟦rt-●⟧ (mk-rt-⟦e⟧ (-W¹ -●/V #f)))
     (for*/union : (℘ -ς) ([C (σ@ σ α)] [Vs (σ@/list σ αs)])
       (define ⟦hv⟧s : (Listof -⟦e⟧)
         (for/list ([V* (in-list Vs)]
                    [i (in-naturals)] #:when (index? i))
           (define ⟦chk⟧
             (mk-mon-⟦e⟧ l³ (ℒ-with-mon ℒ ℓ*)
                         (mk-rt-⟦e⟧ (-W¹ C c))
                         (mk-rt-⟦e⟧ (-W¹ V* (-?@ 'vector-ref sᵥ (-b i))))))
           (mk-app-⟦e⟧ lo ℒ ⟦rt-●⟧ (list ⟦chk⟧))))
       (match-define (cons ⟦e⟧ ⟦e⟧s) (append ⟦hv⟧s (list ⟦erase⟧ ⟦rt⟧)))
       (⟦e⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦e⟧s ⊥ρ ⟦k⟧)))]
    [(-Vector^ αᵥ n)
     (define ⟦erase⟧ (mk-erase-⟦e⟧ (list αᵥ)))
     (for*/union : (℘ -ς) ([C (σ@ σ α)] [V* (σ@ σ αᵥ)])
        (mon l³ $ ℒ (-W¹ C c) (-W¹ V* #|TODO|# #f) Γ ⟪ℋ⟫ Σ
             (bgn∷ (list ⟦erase⟧) ⊥ρ ⟦k⟧)))]
    [(-Vector/hetero αs l³*)
     (define cs : (Listof -s) (for/list ([α : -⟪α⟫ αs]) (⟪α⟫->s α)))
     (for*/union : (℘ -ς) ([C (σ@ σ α)] [Cs (σ@/list σ αs)])
       (define ⟦chk⟧s : (Listof -⟦e⟧)
         (for/list ([C* (in-list Cs)]
                    [c* (in-list cs)]
                    [i (in-naturals)] #:when (index? i))
           (define ⟦inner⟧
             (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓ*)
                         (mk-rt-⟦e⟧ (-W¹ C* c*))
                         (mk-rt-⟦e⟧ (-W¹ -●/V (-?@ 'vector-ref sᵥ (-b i))))))
           (mk-mon-⟦e⟧ l³ ℒ (mk-rt-⟦e⟧ (-W¹ C c)) ⟦inner⟧)))
       (match-define (cons ⟦e⟧ ⟦e⟧s) (append ⟦chk⟧s (list ⟦rt⟧)))
       (⟦e⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦e⟧s ⊥ρ ⟦k⟧)))]
    [(-Vector/homo α* l³*)
     (define c* (⟪α⟫->s α*))
     (for*/union : (℘ -ς) ([C* (σ@ σ α*)] [C (σ@ σ α)])
       (define ⟦chk⟧
         (let ([⟦inner⟧
                (mk-mon-⟦e⟧ l³* (ℒ-with-mon ℒ ℓ*) (mk-rt-⟦e⟧ (-W¹ C* c*))
                            (mk-rt-⟦e⟧ (-W¹ -●/V (-x (+x!/memo 'inner)))))])
           (mk-mon-⟦e⟧ l³ ℒ (mk-rt-⟦e⟧ (-W¹ C c)) ⟦inner⟧)))
       (⟦chk⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ (list ⟦rt⟧) ⊥ρ ⟦k⟧)))]
    [(-● _)
     (define ⟦er⟧ (mk-rt-⟦e⟧ (-blm l+ lo (list 'vector?) (list Vᵥ))))
     (app lo $ ℒ -vector?/W (list W-V) Γ ⟪ℋ⟫ Σ
          (if∷ lo ⟦rt⟧ ⟦er⟧ ⊥ρ ⟦k⟧))]
    [_ (⟦k⟧ (-blm l+ lo (list 'vector?) (list Vᵥ)) $ Γ ⟪ℋ⟫ Σ)]))

(define (mon-vector/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ _ _) Σ)
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ Vᵥ vᵥ) W-V)
  (match-define (-W¹ C  c ) W-C)
  (match-define (-Vector/C αℓs) C)
  ;(printf "mon-vector/c ~a on ~a~n" (show-W¹ W-C) (show-W¹ W-V))
  (define-values (αs ℓs) ((inst unzip -⟪α⟫ -ℓ) αℓs))
  (define n (length αs))
  (define N (let ([b (-b n)]) (-W¹ b b)))
  (define cs
    (let ([ss (-app-split c 'vector/c n)])
      (for/list : (Listof -s) ([s ss] [α : -⟪α⟫ αs])
        (or s (⟪α⟫->s α)))))
  (define ⟦chk-vct⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ -vector?/W) (list (mk-rt-⟦e⟧ W-V))))
  (define ⟦chk-len⟧
    (let ([⟦len⟧ (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ -vector-length/W) (list (mk-rt-⟦e⟧ W-V)))])
      (mk-app-⟦e⟧ lo ℒ (mk-rt-⟦e⟧ -=/W) (list (mk-rt-⟦e⟧ N) ⟦len⟧))))
  (define ⟦blm-vct⟧ (mk-rt-⟦e⟧ (-blm l+ lo (list 'vector?) (list Vᵥ))))
  (define ⟦blm-len⟧ (mk-rt-⟦e⟧ (-blm l+ lo (list (format-symbol "length ~a" n)) (list Vᵥ))))
  (define ⟦mk⟧
    (let ([V* (-Vector/hetero αs l³)])
      (mk-rt-⟦e⟧ (-W (list V*) vᵥ))))
  (define ⟦rt-●⟧ (mk-rt-⟦e⟧ (-W¹ -●/V #f)))
  (for*/union : (℘ -ς) ([Cs (in-set (σ@/list σ αs))])
     (define ⟦hv-fld⟧s : (Listof -⟦e⟧)
       (for/list ([C* (in-list Cs)]
                  [c* (in-list cs)]
                  [ℓᵢ : -ℓ (in-list ℓs)]
                  [i (in-naturals)] #:when (index? i))
         (define W-C* (-W¹ C* c*))
         (define Wᵢ (let ([b (-b i)]) (-W¹ b b)))
         (define ⟦ref⟧
           (mk-app-⟦e⟧ lo (ℒ-with-mon ℒ ℓᵢ)
                       (mk-rt-⟦e⟧ -vector-ref/W)
                       (list (mk-rt-⟦e⟧ W-V)
                             (mk-rt-⟦e⟧ Wᵢ))))
         (define ⟦mon⟧ (mk-mon-⟦e⟧ l³ ℒ (mk-rt-⟦e⟧ W-C*) ⟦ref⟧))
         (mk-app-⟦e⟧ 'havoc ℒ ⟦rt-●⟧ (list ⟦mon⟧))))
     (define ⟦erase⟧
       (match Vᵥ
         [(-Vector αs) (mk-erase-⟦e⟧ αs)]
         [(-Vector^ α n) (mk-erase-⟦e⟧ (list α))]
         [_ ⟦void⟧]))
     (define ⟦wrp⟧ (mk-begin-⟦e⟧ (append ⟦hv-fld⟧s (list ⟦erase⟧ ⟦mk⟧))))
     (⟦chk-vct⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
      (if∷ lo (mk-if-⟦e⟧ lo ⟦chk-len⟧ ⟦wrp⟧ ⟦blm-len⟧) ⟦blm-vct⟧ ⊥ρ ⟦k⟧))))

(define (mon-flat/c l³ $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  ;(printf "mon-flat/c: ~a ~a ~a~n" ℓ (show-W¹ W-C) (show-W¹ W-V))
  (match-define (-l³ l+ _ lo) l³)
  (match-define (-W¹ C _) W-C)
  (match-define (-W¹ V v) W-V)
  (case (MΓ⊢V∈C (-Σ-M Σ) (-Σ-σ Σ) Γ W-V W-C)
    [(✓) (⟦k⟧ (-W (list V) v) $ Γ ⟪ℋ⟫ Σ)]
    [(✗) (⟦k⟧ (-blm l+ lo (list C) (list V)) $ Γ ⟪ℋ⟫ Σ)]
    [(?)
     (app lo $ ℒ W-C (list W-V) Γ ⟪ℋ⟫ Σ
          (if.flat/c∷ (-W (list V) v) (-blm l+ lo (list C) (list V)) ⟦k⟧))]))

(: flat-chk : -l -$ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
(define (flat-chk l $ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
  (match-define (-Σ σ σₖ _) Σ)
  (match-define (-W¹ C c) W-C)
  (match-define (-W¹ V v) W-V)
  (match C
    [(-And/C _ (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (define-values (c₁ c₂)
       (match-let ([(list s₁ s₂) (-app-split c 'and/c 2)])
         (values (or s₁ (⟪α⟫->s α₁)) (or s₂ (⟪α⟫->s α₂)))))
     (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       (define W-C₁ (-W¹ C₁ c₁))
       (define W-C₂ (-W¹ C₂ c₂))
       (flat-chk l $ (ℒ-with-mon ℒ ℓ₁) W-C₁ W-V Γ ⟪ℋ⟫ Σ
                 (fc-and/c∷ l (ℒ-with-mon ℒ ℓ₂) W-C₁ W-C₂ ⟦k⟧)))]
    [(-Or/C _ (cons α₁ ℓ₁) (cons α₂ ℓ₂))
     (define-values (c₁ c₂)
       (match-let ([(list s₁ s₂) (-app-split c 'or/c 2)])
         (values (or s₁ (⟪α⟫->s α₁)) (or s₂ (⟪α⟫->s α₂)))))
     (for*/union : (℘ -ς) ([C₁ (σ@ σ α₁)] [C₂ (σ@ σ α₂)])
       (define W-C₁ (-W¹ C₁ c₁))
       (define W-C₂ (-W¹ C₂ c₁))
       (flat-chk l $ (ℒ-with-mon ℒ ℓ₁) W-C₁ W-V Γ ⟪ℋ⟫ Σ
                 (fc-or/c∷ l (ℒ-with-mon ℒ ℓ₂) W-C₁ W-C₂ W-V ⟦k⟧)))]
    [(-Not/C (cons α ℓ*))
     (define c*
       (match-let ([(list s) (-app-split c 'not/c 1)])
         (or s (⟪α⟫->s α))))
     (for/union : (℘ -ς) ([C* (σ@ σ α)])
       (define W-C* (-W¹ C* c*))
       (flat-chk l $ (ℒ-with-mon ℒ ℓ*) W-C* W-V Γ ⟪ℋ⟫ Σ (fc-not/c∷ l W-C* W-V ⟦k⟧)))]
    [(-St/C _ s αℓs)
     (define-values (αs ℓs) ((inst unzip -⟪α⟫ -ℓ) αℓs))
     (define cs
       (let ([ss (-struct/c-split c s)])
         (for/list : (Listof -s) ([s ss] [α : -⟪α⟫ αs])
           (or s (⟪α⟫->s α)))))
     (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
       (define ⟦chk-field⟧s : (Listof -⟦e⟧)
         (for/list ([Cᵢ (in-list Cs)]
                    [cᵢ (in-list cs)]
                    [ℓᵢ : -ℓ (in-list ℓs)]
                    [i (in-naturals)] #:when (index? i))
           (define ac (-st-ac s i))
           (define ⟦ref⟧ᵢ (mk-app-⟦e⟧ 'Λ ℒ (mk-rt-⟦e⟧ (-W¹ ac ac)) (list (mk-rt-⟦e⟧ W-V))))
           (mk-fc-⟦e⟧ l (ℒ-with-mon ℒ ℓᵢ) (mk-rt-⟦e⟧ (-W¹ Cᵢ cᵢ)) ⟦ref⟧ᵢ)))
       (match ⟦chk-field⟧s
         ['()
          (define p (-st-p s))
          (define ⟦rt⟧ (mk-rt-⟦e⟧ (-W (list -tt (V+ σ V p)) (-?@ 'values -tt v))))
          (app l $ ℒ (-W¹ p p) (list W-V) Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ ⟦ff⟧ ⊥ρ ⟦k⟧))]
         [(cons ⟦chk-field⟧ ⟦chk-field⟧s*)
          (⟦chk-field⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (fc-struct/c∷ l ℒ s '() ⟦chk-field⟧s* ⊥ρ ⟦k⟧))]))]
    [(-x/C α)
     (match-define (-W¹ C c) W-C)
     (match-define (-W¹ V v) W-V)
     (match-define (-x/C ⟪α⟫) C)
     (define x (match-let ([(-α.x/c x*) (-⟪α⟫->-α ⟪α⟫)])
                 (+x!/memo 'fc x*)))
     (define 𝐱 (-x x))
     (for/set: : (℘ -ς) ([C* (σ@ σ ⟪α⟫)])
       (define W-C* (-W¹ C* c))
       (define W-V* (-W¹ V 𝐱))
       (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ #|FIXME hack|# 'fc (list v)))
       (define αₖ (-ℱ x l ℒ W-C* W-V*))
       (σₖ⊔! σₖ αₖ κ)
       (-ς↑ αₖ ⊤Γ ⟪ℋ⟫))]
    [_
     (define ⟦ap⟧ (mk-app-⟦e⟧ l ℒ (mk-rt-⟦e⟧ W-C) (list (mk-rt-⟦e⟧ W-V))))
     (define ⟦rt⟧ (mk-rt-⟦e⟧ (-W (list -tt (V+ σ V C)) (-?@ 'values -tt v))))
     (⟦ap⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ ⟦ff⟧ ⊥ρ ⟦k⟧))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helper frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memo (mon-or/c∷ [l³ : -l³]
                        [ℒ : -ℒ]
                        [Wₗ : -W¹]
                        [Wᵣ : -W¹]
                        [W-V : -W¹]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (Wₗ Wᵣ W-V)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (mon l³ $ ℒ Wᵣ W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(list (-b #t) V)
       (match-define (-W¹ Cₗ _) Wₗ)
       (define v*
         (match s
           [(-@ 'values (list _ v) _) v]
           [#f #f]))
       (⟦k⟧ (-W (list (V+ (-Σ-σ Σ) V Cₗ)) v*) $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (if.flat/c∷ [W-V : -W] [blm : -blm] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-V)
    (match-define (-W Vs v) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V v)])
         #:true  (⟦k⟧ W-V $ Γ₁ ⟪ℋ⟫ Σ)
         #:false (⟦k⟧ blm $ Γ₂ ⟪ℋ⟫ Σ))]
      [_
       (match-define (-blm _ lo _ _) blm)
       (⟦k⟧ (-blm lo 'Λ '(|1 value|) Vs) $ Γ ⟪ℋ⟫ Σ)])))

;; Conditional
(define/memo (if∷ [l : -l] [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V s)])
         #:true  (⟦e⟧₁ ρ $ Γ₁ ⟪ℋ⟫ Σ ⟦k⟧)
         #:false (⟦e⟧₂ ρ $ Γ₂ ⟪ℋ⟫ Σ ⟦k⟧))]
      [_ (⟦k⟧ (-blm l 'Λ '(1-value) (list (format-symbol "~a values" (length Vs)))) $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (and∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (if∷ l ⟦e⟧ ⟦ff⟧ ρ (and∷ l ⟦e⟧s* ρ ⟦k⟧))]))

(define/memo (or∷ [l : -l] [⟦e⟧s : (Listof -⟦e⟧)] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (match ⟦e⟧s
    ['() ⟦k⟧]
    [(cons ⟦e⟧ ⟦e⟧s*) ; TODO propagate value instead
     (if∷ l ⟦tt⟧ ⟦e⟧ ρ (or∷ l ⟦e⟧s* ρ ⟦k⟧))]))

(define/memo (neg∷ [l : -l] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧ (if∷ l ⟦ff⟧ ⟦tt⟧ ⊥ρ ⟦k⟧))

(define/memo (wrap-st∷ [𝒾 : -𝒾]
                       [⟪α⟫s : (Listof -⟪α⟫)]
                       [⟪α⟫ : -⟪α⟫]
                       [l³ : -l³]
                       [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (define αs* : (Listof (Option -⟪α⟫))
    (for/list ([⟪α⟫ (in-list ⟪α⟫s)]
               [i (in-naturals)] #:when (index? i))
      (and (struct-mutable? 𝒾 i) (cast ⟪α⟫ -⟪α⟫))))
  (define V* (-St* 𝒾 αs* ⟪α⟫ l³))
  (define ⟪α⟫s-casted #|FIXME TR|# (cast ⟪α⟫s (Rec X (U -V -W -W¹ -ρ -⟪α⟫ (Listof X) (℘ X)))))
  (define ⟪α⟫-casted #|FIXME TR|# (cast ⟪α⟫ (Rec X (U -V -W -W¹ -ρ -⟪α⟫ (Listof X) (℘ X)))))
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (⟪α⟫s-casted ⟪α⟫-casted)
    (match-define (-W Vs s) A)
    (match-define (list V) Vs) ; only used internally, should be safe
    (σ⊕! (-Σ-σ Σ) ⟪α⟫ V)
    (⟦k⟧ (-W (list V*) s) $ Γ ⟪ℋ⟫ Σ)))

(define/memo (fc-and/c∷ [l : -l]
                        [ℒ : -ℒ]
                        [W-C₁ : -W¹]
                        [W-C₂ : -W¹]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f)) (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)]
      [(list (-b #t) V)
       (match-define (-@ 'values (list _ sᵥ) _) s)
       (match-define (-W¹ C₁ _) W-C₁)
       (flat-chk l $ ℒ W-C₂ (-W¹ (V+ (-Σ-σ Σ) V C₁) sᵥ) Γ ⟪ℋ⟫ Σ ⟦k⟧)])))

(define/memo (fc-or/c∷ [l : -l]
                       [ℒ : -ℒ]
                       [W-C₁ : -W¹]
                       [W-C₂ : -W¹]
                       [W-V : -W¹]
                       [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C₁ W-C₂)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (flat-chk l $ ℒ W-C₂ W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(list (-b #t) V)
       (match-define (-W¹ C₁ _) W-C₁)
       (⟦k⟧ (-W (list -tt (V+ (-Σ-σ Σ) V C₁)) s) $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (fc-not/c∷ [l : -l]
                        [W-C* : -W¹]
                        [W-V : -W¹]
                        [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C* W-V)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (match-define (-W¹ V v) W-V)
       (⟦k⟧ (-W (list -tt V) (-?@ 'values -tt v)) $ Γ ⟪ℋ⟫ Σ)]
      [(list (-b #t) V)
       (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (fc-struct/c∷ [l : -l]
                           [ℒ : -ℒ]
                           [𝒾 : -𝒾]
                           [W-Vs-rev : (Listof -W¹)]
                           [⟦e⟧s : (Listof -⟦e⟧)]
                           [ρ : -ρ]
                           [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-Vs-rev ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list (-b #f))
       (⟦k⟧ -False/W $ Γ ⟪ℋ⟫ Σ)]
      [(list (-b #t) V*)
       (define v*
         (match s
           [(-@ 'values (list _ v) _) v]
           [#f #f]))
       (match ⟦e⟧s
         ['()
          (define ⟦k⟧*
            (let ([k (-st-mk 𝒾)])
              (ap∷ (append W-Vs-rev (list (-W¹ k k))) '() ⊥ρ l ℒ
                   (ap∷ (list (-W¹ -tt -tt) (-W¹ 'values 'values)) '() ⊥ρ l ℒ ⟦k⟧))))
          (⟦k⟧* (-W (list V*) v*) $ Γ ⟪ℋ⟫ Σ)]
         [(cons ⟦e⟧ ⟦e⟧s*)
          (define W* (-W¹ V* v*))
          (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc-struct/c∷ l ℒ 𝒾 (cons W* W-Vs-rev) ⟦e⟧s* ρ ⟦k⟧))])])))

(define/memo (fc.v∷ [l : -l]
                    [ℒ : -ℒ]
                    [⟦v⟧ : -⟦e⟧]
                    [ρ : -ρ]
                    [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (ρ)
    (match-define (-W Vs s) A)
    (match Vs
      [(list C)
       (⟦v⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.c∷ l ℒ (-W¹ C s) ⟦k⟧))]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

(define/memo (fc.c∷ [l : -l]
                    [ℒ : -ℒ]
                    [W-C : -W¹]
                    [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (with-error-handling (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ) #:roots (W-C)
    (match-define (-W Vs s) A)
    (match Vs
      [(list V)
       (flat-chk l $ ℒ W-C (-W¹ V s) Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helper expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memo (mk-mon-⟦e⟧ [l³ : -l³] [ℒ : -ℒ] [⟦c⟧ : -⟦e⟧] [⟦e⟧ : -⟦e⟧]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (mon.v∷ l³ ℒ (cons ⟦e⟧ ρ) ⟦k⟧))))

(define/memo (mk-app-⟦e⟧ [l : -l] [ℒ : -ℒ] [⟦f⟧ : -⟦e⟧] [⟦x⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦f⟧ ρ $ Γ ⟪ℋ⟫ Σ (ap∷ '() ⟦x⟧s ρ l ℒ ⟦k⟧))))

(define/memo (mk-rt-⟦e⟧ [A : (U -A -W¹)]) : -⟦e⟧
  (match A
    [(-W¹ V v) (mk-rt-⟦e⟧ (-W (list V) v))]
    [(? -A?) (λ (_ $ Γ ⟪ℋ⟫ Σ ⟦k⟧) (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))]))

(define/memo (mk-erase-⟦e⟧ [⟪α⟫s : (Listof -⟪α⟫)]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-Σ σ _ _) Σ)
    (for ([⟪α⟫ : -⟪α⟫ ⟪α⟫s])
      (σ⊕! σ ⟪α⟫ -●/V #:mutating? #t))
    (⟦k⟧ -Void/W $ Γ ⟪ℋ⟫ Σ)))

(define/memo (mk-begin-⟦e⟧ [⟦e⟧s : (Listof -⟦e⟧)]) : -⟦e⟧
  (match ⟦e⟧s
    ['() ⟦void⟧]
    [(cons ⟦e⟧ ⟦e⟧s*)
     (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
       (⟦e⟧ ρ $ Γ ⟪ℋ⟫ Σ (bgn∷ ⟦e⟧s* ρ ⟦k⟧)))]))

(define/memo (mk-if-⟦e⟧ [l : -l]
                       [⟦e⟧₁ : -⟦e⟧]
                       [⟦e⟧₂ : -⟦e⟧]
                       [⟦e⟧₃ : -⟦e⟧]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦e⟧₁ ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦e⟧₂ ⟦e⟧₃ ρ ⟦k⟧))))

(define/memo (mk-fc-⟦e⟧ [l : -l]
                       [ℒ : -ℒ]
                       [⟦c⟧ : -⟦e⟧]
                       [⟦v⟧ : -⟦e⟧]) : -⟦e⟧
  (λ (ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (⟦c⟧ ρ $ Γ ⟪ℋ⟫ Σ (fc.v∷ l ℒ ⟦v⟧ ρ ⟦k⟧))))

(define/memo (make-memoized-⟦k⟧ [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (define-type Key (List -A -Γ -⟪ℋ⟫ (HashTable -⟪α⟫ (℘ -V))))
  (let ([m : (HashTable Key (℘ -ς)) (make-hash)])
    (define ⟦k⟧* : -⟦k⟧
      (λ (A $ Γ ⟪ℋ⟫ Σ)
        (match-define (-Σ (-σ mσ _ _) _ _) Σ)
        (define mσ* (hash-copy/spanning* mσ
                                         (∪ (⟦k⟧->roots ⟦k⟧)
                                            (match A
                                              [(-W Vs _) (->⟪α⟫s Vs)]
                                              [_ ∅eq]))
                                         V->⟪α⟫s))
        (define k : Key (list A Γ ⟪ℋ⟫ mσ*))
        #;(when (hash-has-key? m k)
          (printf "hit-k~n"))
        (hash-ref! m k (λ () (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ)))))
    (add-⟦k⟧-roots! ⟦k⟧* (⟦k⟧->roots ⟦k⟧))
    (set-⟦k⟧->αₖ! ⟦k⟧* (⟦k⟧->αₖ ⟦k⟧))
    ⟦k⟧*))
