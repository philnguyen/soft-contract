#lang typed/racket/base

(provide app@)

(require racket/set
         racket/match
         (only-in racket/list split-at)
         typed/racket/unit
         syntax/parse/define
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit app@
  (import ast-pretty-print^ static-info^
          mon^ compile^ kont^ proof-system^ local-prover^ prims^ memoize^ widening^
          env^ val^ pc^ instr^ sto^ pretty-print^ for-gc^)
  (export app^)

  (: app : ℓ -W¹ (Listof -W¹) -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  (define (app ℓ Wₕ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #;(printf "app ~a: ~a to ~a knowing ~a~n" (show-ℓ ℓ) (show-W¹ Wₕ) (map show-W¹ Wₓs) (show-Γ Γ))
    (match-define (-W¹ Vₕ sₕ) Wₕ)
    (define l (ℓ-src ℓ))
    (define σ (-Σ-σ Σ))

    (: blm-arity : Arity Natural → -blm)
    (define (blm-arity required provided)
      ;; HACK for error message. Probably no need to fix
      (define msg (format-symbol "require ~a arguments"
                                 (string->symbol (format "~a" required))))
      (-blm l 'Λ (list msg) (map -W¹-V Wₓs) ℓ))

    (define-syntax-rule (with-guarded-arity a* e ...)
      (let ([n (length Wₓs)]
            [a a*])
        (cond
          [(arity-includes? a n) e ...]
          [else (⟦k⟧ (blm-arity a n) $ Γ ⟪ℋ⟫ Σ)])))

    (define (app-And/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
      (define ⟦rhs⟧ (mk-app ℓ (mk-rt W₂) (list (mk-rt (car Wₓs)))))
      (app ℓ W₁ Wₓs $ Γ ⟪ℋ⟫ Σ (and∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))

    (define (app-Or/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
      (define ⟦rhs⟧ (mk-app ℓ (mk-rt W₂) (list (mk-rt (car Wₓs)))))
      (app ℓ W₁ Wₓs $ Γ ⟪ℋ⟫ Σ (or∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))
    
    (define (app-Not/C [Wᵤ : -W¹]) : (℘ -ς)
      (app ℓ Wᵤ Wₓs $ Γ ⟪ℋ⟫ Σ (ap∷ (list (+W¹ 'not)) '() ⊥ρ ℓ ⟦k⟧)))

    (define (app-One-Of/C [bs : (℘ Base)]) : (℘ -ς)
      (match-define (list (-W¹ Vₓ sₓ)) Wₓs)
      (define Wₐ
        (case (sat-one-of Vₓ bs)
          [(✓) (+W (list -tt))]
          [(✗) (+W (list -ff))]
          [(?) (-W (list (+● 'boolean?)) (?t@ (-One-Of/C bs) sₓ))]))
      (⟦k⟧ Wₐ $ Γ ⟪ℋ⟫ Σ))

    (define (app-St/C [𝒾 : -𝒾] [W-Cs : (Listof -W¹)]) : (℘ -ς)
      ;; TODO fix ℓ
      (match-define (list Wₓ) Wₓs)
      (match-define (-W¹ Vₓ _) Wₓ)
      (match Vₓ
        [(or (-St (== 𝒾) _) (-St* (-St/C _ (== 𝒾) _) _ _))
         (define ⟦chk-field⟧s : (Listof -⟦e⟧)
           (for/list ([W-C (in-list W-Cs)]
                      [i (in-naturals)] #:when (index? i))
             (define Ac (let ([ac (-st-ac 𝒾 i)]) (-W¹ ac ac)))
             (mk-app ℓ (mk-rt W-C)
                         (list (mk-app ℓ (mk-rt Ac) (list (mk-rt Wₓ)))))))
         (define P (let ([p (-st-p 𝒾)]) (-W¹ p p)))
         (app ℓ P (list Wₓ) $ Γ ⟪ℋ⟫ Σ (and∷ l ⟦chk-field⟧s ⊥ρ ⟦k⟧))]
        [_
         (⟦k⟧ (+W (list -ff)) $ Γ ⟪ℋ⟫ Σ)]))

    (match Vₕ
      ;; In the presence of struct contracts, field accessing is not an atomic operation
      ;; because structs can be contract-wrapped arbitrarily deeply,
      ;; plus contracts can be arbitrary code.
      ;; This means field accessing cannot be implemented in `δ`
      [(-st-p  𝒾) ((app-st-p 𝒾) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-st-mk 𝒾) ((app-st-mk 𝒾) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-st-ac  𝒾 i) ((app-st-ac  𝒾 i) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-st-mut 𝒾 i) ((app-st-mut 𝒾 i) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      ['make-sequence (app-make-sequence ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]

      ;; Regular stuff
      [(? symbol? o) ((app-prim o) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-Clo xs ⟦e⟧ ρₕ Γₕ)
       (with-guarded-arity (shape xs)
         ((app-clo xs ⟦e⟧ ρₕ Γₕ sₕ) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧))]
      [(-Case-Clo clauses ρₕ Γₕ)
       ((app-Case-Clo clauses ρₕ Γₕ sₕ) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [(-Ar C α l³)
       (with-guarded-arity (guard-arity C)
         (define-values (c _) (-ar-split sₕ))
         (cond
           [(-=>? C)
            (for/union : (℘ -ς) ([Vᵤ (σ@ Σ α)] #:unless (equal? Vₕ Vᵤ))
                       ((app-Ar C c Vᵤ sₕ l³) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧))]
           [(-=>i? C)
            (for/union : (℘ -ς) ([Vᵤ (σ@ Σ α)] #:unless (equal? Vₕ Vᵤ))
                       ((app-Indy C c Vᵤ sₕ l³) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧))]
           [else
            (for/union : (℘ -ς) ([Vᵤ (σ@ Σ α)] #:unless (equal? Vₕ Vᵤ))
                       ((app-guarded-Case C c Vᵤ sₕ l³) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧))]))]
      [(-And/C #t (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (with-guarded-arity 1
         (match-define (list c₁ c₂) (-app-split 'and/c sₕ 2))
         (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
                     (app-And/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
      [(-Or/C #t (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (with-guarded-arity 1
         (match-define (list c₁ c₂) (-app-split 'or/c sₕ 2))
         (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
                     (app-Or/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
      [(-Not/C (-⟪α⟫ℓ α ℓ*))
       (with-guarded-arity 1
         (match-define (list c*) (-app-split 'not/c sₕ 1))
         (for/union : (℘ -ς) ([C* (σ@ Σ α)])
                    (app-Not/C (-W¹ C* c*))))]
      [(-One-Of/C vals)
       (with-guarded-arity 1
         (app-One-Of/C vals))]
      [(-St/C #t s αℓs)
       (with-guarded-arity 1
         (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
         (define cs (-struct/c-split sₕ s))
         (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
                    (app-St/C s (map -W¹ Cs cs))))]
      [(or (? -●?) (? -Fn●?)) ;; TODO clean this mess up

       (define l (ℓ-src ℓ))

       (: blm : -V → -Γ → (℘ -ς))
       (define ((blm C) Γ)
         (define blm (-blm l 'Λ (list C) (list Vₕ) ℓ))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

       (: chk-arity : -Γ → (℘ -ς))
       (define (chk-arity Γ)
         (define required-arity
           (let ([b (-b (length Wₓs))])
             (-W¹ b b)))
         (define Wₕ-arity
           (let ([Vₐ (V-arity Vₕ)]
                 [sₐ (?t@ 'procedure-arity sₕ)])
             (-W¹ (if Vₐ (-b Vₐ) (+●)) sₐ)))
         (with-Γ+/-oW (σ Γ 'arity-includes? Wₕ-arity required-arity)
           #:on-t do-app
           #:on-f (blm (format-symbol "(arity-includes/c ~a)" (length Wₓs)))))

       (: do-app : -Γ → (℘ -ς))
       (define (do-app Γ)
         ((app-opq sₕ) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧))
       
       (with-Γ+/-oW (σ Γ 'procedure? Wₕ)
         #:on-t chk-arity
         #:on-f (blm 'procedure?))]
      [_
       (define blm (-blm l 'Λ (list 'procedure?) (list Vₕ) ℓ))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))

  (: app-prim : Symbol → -⟦f⟧)
  (define (app-prim o)
    (λ (ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match (get-prim o)
        [(-⟦o⟧.boxed ⟦o⟧)
         #;(begin
           (printf "~a ~a~n" (show-o o) (map show-W¹ Wₓs))
           (printf "  - knowing: ~a~n" (show-Γ Γ))
           (for ([ans (in-set (⟦o⟧ ⟪ℋ⟫ ℓ Σ $ Γ Wₓs))])
             (printf "  - ~a~n" (show-ΓA ans)))
           (printf "~n"))
         (for/union : (℘ -ς) ([ΓA (in-set (⟦o⟧ ⟪ℋ⟫ ℓ Σ $ Γ Wₓs))])
           (match-define (-ΓA Γₐ A) ΓA)
           (⟦k⟧ A $ Γₐ ⟪ℋ⟫ Σ))]
        [(-⟦f⟧.boxed ⟦f⟧)
         (⟦f⟧ ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)])))

  (: app-clo : -formals -⟦e⟧ -ρ -Γ -?t → -⟦f⟧)
  (define (app-clo xs ⟦e⟧ ρₕ Γₕ sₕ)
    (λ (ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-t Wₓs))
      (define-values (⟪ℋ⟫ₑₑ looped?) (⟪ℋ⟫+ ⟪ℋ⟫ (-edge ⟦e⟧ ℓ)))
      (define ρₕ.dom (dom ρₕ))
      (define unsure-locs (unsure-locations ρₕ.dom (-λ? sₕ) looped?))
      (define $₀ (if looped? ($-del* ($-del* $ unsure-locs) (bound-vars ⟦e⟧)) ($-del* $ unsure-locs))) ; FIXME do it properly

      ;; Target's environment
      (define-values (ρ* $*)
        (match xs
          [(? list? xs)
           (alloc-init-args! Σ $₀ Γ ρₕ ⟪ℋ⟫ₑₑ xs Wₓs looped?)]
          [(-var zs z)
           (define-values (Ws₀ Wsᵣ) (split-at Wₓs (length zs)))
           (define-values (ρ₀ $₁) (alloc-init-args! Σ $₀ Γ ρₕ ⟪ℋ⟫ₑₑ zs Ws₀ looped?))
           (define Vᵣ (alloc-rest-args! Σ Γ ⟪ℋ⟫ₑₑ ℓ Wsᵣ))
           (define αᵣ (-α->⟪α⟫ (-α.x z ⟪ℋ⟫ₑₑ)))
           (σ⊕V! Σ αᵣ Vᵣ)
           (values (ρ+ ρ₀ z αᵣ) ($-set $₁ z z))]))

      (define $**
        (let ([root (∪ (ρ->⟪α⟫s ρ*) (⟦k⟧->⟪α⟫s ⟦k⟧ (-Σ-σₖ Σ)))])
          ($-cleanup (gc-$ $* (-Σ-σ Σ) root))))
      (define Γₕ*
        (if looped? Γₕ (copy-Γ ($-symbolic-names $*) Γₕ Γ))
        #;(for/fold ([Γ : -Γ (if looped? Γₕ (copy-Γ $* Γₕ Γ))])
                  ([x (if (list? xs) xs (-var-init xs))]
                   [Wₓ (in-list Wₓs)])
          (match-define (-W¹ Vₓ tₓ) Wₓ)
          (for*/fold ([Γ : -Γ Γ])
                     ([tₓ* (in-value (hash-ref $** x #f))]
                      #:when tₓ*
                      [h (in-set (∪ (predicates-of-V Vₓ) (predicates-of Γ tₓ)))]
                      [t (in-value (-t.@ h (list tₓ*)))]
                      #:when t
                      #:unless (equal? '✓ (Γ⊢t Γ t)))
            (Γ+ Γ t))))
      (define αₖ (-ℬ $** ⟪ℋ⟫ₑₑ xs ⟦e⟧ ρ* Γₕ*))
      (define κ
        (let* ([δ$ ($-extract $ (match xs [(-var zs z) (cons z zs)] [(? list?) xs]))]
               [⟦k⟧* (invalidate-$∷ unsure-locs (restore-$∷ δ$ (restore-ctx∷ ⟪ℋ⟫ ⟦k⟧)))])
          (-κ.rt ⟦k⟧* ($-symbolic-names $) Γ (apply ?t@ sₕ sₓs) looped?)))
      (σₖ⊕! Σ αₖ κ)
      {set (-ς↑ αₖ)}))

  (: app-Case-Clo : (Listof (Pairof (Listof Symbol) -⟦e⟧)) -ρ -Γ -?t → -⟦f⟧)
  (define ((app-Case-Clo clauses ρₕ Γₕ sₕ) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define n (length Wₓs))
    (define clause
      (for/or : (Option (Pairof (Listof Symbol) -⟦e⟧)) ([clause clauses])
        (match-define (cons xs _) clause)
        (and (equal? n (length xs)) clause)))
    (cond
      [clause
       (match-define (cons xs ⟦e⟧) clause)
       ((app-clo xs ⟦e⟧ ρₕ Γₕ sₕ) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
      [else
       (define a : (Listof Index) (for/list ([clause clauses]) (length (car clause))))
       (define l (ℓ-src ℓ))
       (define blm (-blm l 'Λ
                         (list (format-symbol "arity in ~a" (string->symbol (format "~a" a))))
                         (map -W¹-V Wₓs) ℓ))
       (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))

  (: app-guarded-Case : -V -?t -V -?t -l³ → -⟦f⟧)
  (define ((app-guarded-Case C c Vᵤ sₕ l³) ℓ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (error 'app-guarded-Case "TODO"))

  (: app-Ar : -=> -?t -V -?t -l³ → -⟦f⟧)
  (define ((app-Ar C c Vᵤ sₕ l³) ℓₐ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (match-define (-l³ l+ l- lo) l³)
    (define Wᵤ (-W¹ Vᵤ sₕ)) ; inner function
    (match-define (-=> αℓs Rng _) C)
    (define-values (cs d) (-->-split c (shape αℓs)))
    (define l³* (-l³ l- l+ lo))
    (define ⟦k⟧/mon-rng (mon*.c∷ l³ ℓₐ Rng d ⟦k⟧))
    (define ℓₐ* (ℓ-with-src ℓₐ lo))
    (match* (αℓs cs)
      [('() '()) ; no arg
       (app ℓₐ* Wᵤ '() $ Γ ⟪ℋ⟫ Σ ⟦k⟧/mon-rng)]
      [((? pair?) (? pair?))
       (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
       (for*/union : (℘ -ς) ([Cs (in-set (σ@/list σ αs))])
         (match-define (cons ⟦mon-x⟧ ⟦mon-x⟧s)
           (for/list : (Listof -⟦e⟧) ([C Cs]
                                      [c cs]
                                      [Wₓ Wₓs]
                                      [ℓₓ : ℓ ℓs])
             (mk-mon l³* ℓₓ (mk-rt (-W¹ C c)) (mk-rt Wₓ))))
         (⟦mon-x⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
          (ap∷ (list Wᵤ) ⟦mon-x⟧s ⊥ρ ℓₐ* ⟦k⟧/mon-rng)))]
      [((-var αℓs₀ αℓᵣ) (-var cs₀ cᵣ))
       (define-values (αs₀ ℓs₀) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs₀))
       (match-define (-⟪α⟫ℓ αᵣ ℓᵣ) αℓᵣ)
       (define-values (Ws₀ Wsᵣ) (split-at Wₓs (length αs₀)))
       (define Vᵣ (alloc-rest-args! Σ Γ ⟪ℋ⟫ ℓᵣ Wsᵣ))
       (define Wᵣ (-W¹ Vᵣ (-?list (map -W¹-t Wsᵣ))))
       (for*/union : (℘ -ς) ([Cs₀ (in-set (σ@/list σ αs₀))]
                             [Cᵣ (in-set (σ@ Σ αᵣ))])
         (define ⟦mon-x⟧s : (Listof -⟦e⟧)
           (for/list ([Cₓ Cs₀] [cₓ cs₀] [Wₓ Ws₀] [ℓₓ : ℓ ℓs₀])
             (mk-mon l³* ℓₓ (mk-rt (-W¹ Cₓ cₓ)) (mk-rt Wₓ))))
         (define ⟦mon-x⟧ᵣ : -⟦e⟧
           (mk-mon l³* ℓᵣ (mk-rt (-W¹ Cᵣ cᵣ)) (mk-rt Wᵣ)))
         (match ⟦mon-x⟧s
           ['()
            (⟦mon-x⟧ᵣ ⊥ρ $ Γ ⟪ℋ⟫ Σ
             (ap∷ (list Wᵤ (+W¹ 'apply)) '() ⊥ρ ℓₐ* ⟦k⟧/mon-rng))]
           [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
            (⟦mon-x⟧₀ ⊥ρ $ Γ ⟪ℋ⟫ Σ
             (ap∷ (list Wᵤ (+W¹ 'apply)) `(,@ ⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ ℓₐ* ⟦k⟧/mon-rng))]))]))

  (: apply-app-Ar : (-=> -?t -V -?t -l³ → ℓ (Listof -W¹) -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))
  (define ((apply-app-Ar C c Vᵤ sₕ l³) ℓ Ws₀ Wᵣ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-=> (-var αℓs₀ (-⟪α⟫ℓ αᵣ ℓᵣ)) (-⟪α⟫ℓ β ℓₐ) _) C)
    (match-define-values ((-var cs₀ cᵣ) d) (-->-split c (arity-at-least (length αℓs₀))))
    ;; FIXME copied n pasted from app-Ar
    (define-values (αs₀ ℓs₀) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs₀))
    (match-define (-W¹ Vᵣ sᵣ) Wᵣ)
    (match-define (-l³ l+ l- lo) l³)
    (define l³* (-l³ l- l+ lo))
    (define Wᵤ (-W¹ Vᵤ sₕ))
    (for*/union : (℘ -ς) ([Cs₀ (in-set (σ@/list Σ αs₀))]
                          [Cᵣ (in-set (σ@ Σ αᵣ))]
                          [D (in-set (σ@ Σ β))])
      (define ⟦mon-x⟧s : (Listof -⟦e⟧)
        (for/list ([Cₓ Cs₀] [cₓ cs₀] [Wₓ Ws₀] [ℓₓ : ℓ ℓs₀])
          (mk-mon l³* ℓₓ (mk-rt (-W¹ Cₓ cₓ)) (mk-rt Wₓ))))
      (define ⟦mon-x⟧ᵣ : -⟦e⟧
        (mk-mon l³* ℓᵣ (mk-rt (-W¹ Cᵣ cᵣ)) (mk-rt Wᵣ)))
      (match ⟦mon-x⟧s
        ['()
         (⟦mon-x⟧ᵣ ⊥ρ Γ ⟪ℋ⟫ Σ
          (ap∷ (list Wᵤ (+W¹ 'apply)) '() ⊥ρ ℓ
               (mon.c∷ l³ ℓₐ (-W¹ D d) ⟦k⟧)))]
        [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
         (⟦mon-x⟧₀ ⊥ρ Γ ⟪ℋ⟫ Σ
          (ap∷ (list Wᵤ (+W¹ 'apply)) `(,@ ⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ ℓ
               (mon.c∷ l³ ℓₐ (-W¹ D d) ⟦k⟧)))])))

  (: app-Indy : -=>i -?t -V -?t -l³ → -⟦f⟧)
  (define ((app-Indy C c Vᵤ sₕ l³) ℓₐ Wₓs $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-l³ l+ l- lo) l³)
    (define l³* (-l³ l- l+ lo))
    (define Wᵤ (-W¹ Vᵤ sₕ)) ; inner function
    (match-define (-=>i αℓs (list Mk-D mk-d ℓᵣ) _) C)
    (match-define (-Clo xs ⟦d⟧ ρᵣ _) Mk-D)
    (define W-rng (-W¹ Mk-D mk-d))
    (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
    (define-values (cs _) (-->i-split c (length αℓs)))
    (define ℓₐ* (ℓ-with-src ℓₐ lo))
    (match xs
      [(? list?)
       (define ⟦x⟧s : (Listof -⟦e⟧) (for/list ([x (in-list xs)]) (↓ₓ lo x (loc->ℓ (loc 'indy 0 0 (list x))))))
       (define ⟦app⟧ (mk-app ℓₐ* (mk-rt Wᵤ) ⟦x⟧s))
       (define ⟦rng⟧
         (cond [(-λ? mk-d) (assert (equal? xs (-λ-_0 mk-d))) ⟦d⟧]
               [else (mk-app ℓₐ (mk-rt W-rng) ⟦x⟧s)]))
       (define ⟦mon-app⟧ (mk-mon l³ ℓᵣ ⟦rng⟧ ⟦app⟧))
       (define ρᵣ* : -ρ (if (-λ? mk-d) ρᵣ ⊥ρ))
       (for/union : (℘ -ς) ([Cs (in-set (σ@/list Σ αs))])
         (define ⟦mon-x⟧s : (Listof -⟦e⟧)
           (for/list ([C (in-list Cs)]
                      [c (in-list cs)]
                      [Wₓ (in-list Wₓs)]
                      [ℓₓ : ℓ (in-list ℓs)])
             (mk-mon l³* ℓₓ (mk-rt (-W¹ C c)) (mk-rt Wₓ))))
         (match* (xs ⟦x⟧s ⟦mon-x⟧s)
           [('() '() '())
            (⟦mon-app⟧ ρᵣ* $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
           [((cons x xs*) (cons ⟦x⟧ ⟦x⟧s*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
            (⟦mon-x⟧ ρᵣ* $ Γ ⟪ℋ⟫ Σ
             (let∷ ℓₐ
                   (list x)
                   (for/list ([xᵢ (in-list xs*)] [⟦mon⟧ᵢ (in-list ⟦mon-x⟧s*)])
                     (cons (list xᵢ) ⟦mon⟧ᵢ))
                   '()
                   ⟦mon-app⟧
                   ρᵣ*
                    ⟦k⟧))]))]
      [(-var zs z)
       (error 'app-Indy "TODO: varargs in ->i: ~a" (cons zs z))]))

  (define (app-st-p [𝒾 : -𝒾]) : -⟦f⟧
    (define st-p (-st-p 𝒾))
    (λ (ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match Ws
        [(list (and W (-W¹ _ s)))
         (define sₐ (?t@ st-p s))
         (define A
           (case (Γ⊢oW (-Σ-σ Σ) Γ st-p W)
             [(✓) -tt]
             [(✗) -ff]
             [(?) (+● 'boolean?)]))
         (⟦k⟧ (-W (list A) sₐ) $ Γ ⟪ℋ⟫ Σ)]
        [_
         (define blm (blm-arity ℓ (show-o st-p) 1 (map -W¹-V Ws)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define (app-st-mk [𝒾 : -𝒾]) : -⟦f⟧
    (define st-mk (-st-mk 𝒾))
    (define n (count-struct-fields 𝒾))
    (λ (ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (cond
        [(= n (length Ws))
         (define tₐ ℓ)
         (define σ (-Σ-σ Σ))
         (define-values ($* αs.rev)
           (for/fold ([$ : -$ $]
                      [αs.rev : (Listof ⟪α⟫) '()])
                     ([W (in-list Ws)]
                      [i : Index n])
             (match-define (-W¹ V t) W)
             (define V* (V+ σ V (predicates-of Γ t)))
             (define α (-α->⟪α⟫ (-α.fld 𝒾 ℓ ⟪ℋ⟫ i)))
             (σ⊕V! Σ α V*)
             (define l (-loc.offset 𝒾 i tₐ))
             (values ($-set! Σ $ α l t) (cons α αs.rev))))
         (define V (-St 𝒾 (reverse αs.rev)))
         (⟦k⟧ (-W (list V) tₐ) $* Γ ⟪ℋ⟫ Σ)]
        [else
         (define blm (blm-arity ℓ (show-o st-mk) n (map -W¹-V Ws)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)])))

  (define (app-st-ac [𝒾 : -𝒾] [i : Index]) : -⟦f⟧
    (define ac (-st-ac 𝒾 i))
    (define p  (-st-p 𝒾))
    (define n (count-struct-fields 𝒾))
    
    (: ⟦ac⟧ : -⟦f⟧)
    (define (⟦ac⟧ ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match Ws
        [(list (and W (-W¹ V s)))
         (define l (ℓ-src ℓ))
         (define (blm) (-blm l (show-o ac) (list p) (list V) ℓ))
         (match V
           [(-St 𝒾* αs) #:when (𝒾* . substruct? . 𝒾)
            (define α (list-ref αs i))
            (cond
              [s
               (define l (-loc.offset 𝒾 i s))
               (define-values (Ws $*) ($@! Σ Γ α $ l ℓ))
               (for/union : (℘ -ς) ([W (in-set Ws)])
                 (⟦k⟧ (W¹->W W) $* Γ ⟪ℋ⟫ Σ))]
              [else
               (for/union : (℘ -ς) ([V (in-set (σ@ Σ α))])
                 (⟦k⟧ (-W (list V) #f) $ Γ ⟪ℋ⟫ Σ))])]
           [(-St* (-St/C _ 𝒾* αℓs) α l³) #:when (𝒾* . substruct? . 𝒾)
            (define ℓ/ignore (ℓ-with-src ℓ 'st-ac))
            (match-define (-l³ _ _ lₒ) l³)
            (define Ac (-W¹ ac ac))
            (cond
              ;; mutable field should be wrapped
              [(struct-mutable? 𝒾 i)
               (match-define (-⟪α⟫ℓ αᵢ ℓᵢ) (list-ref αℓs i))
               (define Cᵢs (σ@ Σ αᵢ))
               (define Vs  (σ@ Σ α))
               (define cᵢ #f #;(⟪α⟫->s αᵢ))
               (for*/union : (℘ -ς) ([Cᵢ (in-set Cᵢs)] [V* (in-set Vs)])
                 (⟦ac⟧ ℓ/ignore (list (-W¹ V* s)) $ Γ ⟪ℋ⟫ Σ
                  (mon.c∷ l³ ℓᵢ (-W¹ Cᵢ cᵢ) ⟦k⟧)))]
              ;; no need to check immutable field
              [else
               ;; TODO: could this loop forever due to cycle?
               (for/union : (℘ -ς) ([V* (in-set (σ@ Σ α))])
                 (⟦ac⟧ ℓ/ignore (list (-W¹ V* s)) $ Γ ⟪ℋ⟫ Σ ⟦k⟧))])]
           [(-● ps)
            (with-Γ+/- ([(Γₒₖ Γₑᵣ) (Γ+/-oW (-Σ-σ Σ) Γ p W)])
              #:true  (⟦k⟧ (-W (if (and (equal? 𝒾 -𝒾-cons) (equal? i 1) (∋ ps 'list?))
                                   (list (-● {set 'list?}))
                                   (list (+●)))
                               (?t@ ac s))
                       $ Γₒₖ ⟪ℋ⟫ Σ)
              #:false (⟦k⟧ (blm) $ Γₑᵣ ⟪ℋ⟫ Σ))]
           [_ (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)])]
        [_
         (define blm (blm-arity ℓ (show-o ac) 1 (map -W¹-V Ws)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
    ⟦ac⟧)

  (define (app-st-mut [𝒾 : -𝒾] [i : Index]) : -⟦f⟧
    (define mut (-st-mut 𝒾 i))
    (define p (-st-p 𝒾))
    
    (: ⟦mut⟧ : -⟦f⟧)
    (define (⟦mut⟧ ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (match Ws
        [(list Wₛ Wᵥ)
         (match-define (-W¹ Vₛ sₛ) Wₛ)
         (match-define (-W¹ Vᵥ tᵥ) Wᵥ)
         (define l (ℓ-src ℓ))
         (define (blm) (-blm l (show-o mut) (list p) (list Vₛ) ℓ))
         
         (match Vₛ
           [(-St (== 𝒾) αs)
            (define α (list-ref αs i))
            (σ⊕! Σ Γ α Wᵥ)
            (define $* (if sₛ
                           ($-set! Σ $ α (-loc.offset 𝒾 i sₛ) tᵥ)
                           ($-del* $ (get-aliases Σ α))))
            (⟦k⟧ (+W (list -void)) $* Γ ⟪ℋ⟫ Σ)]
           [(-St* (-St/C _ (== 𝒾) γℓs) α l³)
            (define ℓ/ignore (ℓ-with-src ℓ 'st-mut))
            (match-define (-l³ l+ l- lo) l³)
            (define l³* (-l³ l- l+ lo))
            (match-define (-⟪α⟫ℓ γ ℓᵢ) (list-ref γℓs i))
            (define c #f #;(⟪α⟫->s γ))
            (define Mut (-W¹ mut mut))
            (for*/union : (℘ -ς) ([Vₛ* (in-set (σ@ Σ α))]
                                  [⟦k⟧* (in-value (ap∷ (list (-W¹ Vₛ* sₛ) Mut) '() ⊥ρ ℓ/ignore ⟦k⟧))]
                                  [C (in-set (σ@ Σ γ))])
              (push-mon l³* ℓᵢ (-W¹ C c) Wᵥ $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]
           [(-● _)
            (with-Γ+/-oW ((-Σ-σ Σ) Γ p Wₛ)
              #:on-t (λ ([Γ : -Γ])
                       (add-leak! Σ (-W¹-V Wᵥ))
                       (⟦k⟧ (+W (list -void)) $ Γ ⟪ℋ⟫ Σ))
              #:on-f (λ ([Γ : -Γ])
                       (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)))]
           [_ (⟦k⟧ (blm) $ Γ ⟪ℋ⟫ Σ)])]
        [_
         (define blm (blm-arity ℓ (show-o mut) 2 (map -W¹-V Ws)))
         (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ)]))
    ⟦mut⟧)

  ;; FIXME tmp hack for `make-sequence` use internallyr
  (: app-make-sequence : -⟦f⟧)
  (define (app-make-sequence ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define Vs (list -car -cdr 'values -one -cons? -ff -ff))
    (define t (-t.@ 'values (list -car -cdr 'values -one -cons? -ff -ff)))
    (define A (-W Vs t))
    (⟦k⟧ A $ Γ ⟪ℋ⟫ Σ))

  (define (app-opq [sₕ : -?t]) : -⟦f⟧
    (λ (ℓ Ws $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
      (define tₐ ℓ #|TODO make sure ok|#)
      (for ([W (in-list Ws)])
        (add-leak! Σ (-W¹-V W)))
      (define αₖ (-ℋ𝒱 $ ⟪ℋ⟫))
      (define κ (-κ.rt (bgn0.e∷ (-W (list (+●)) tₐ) '() ⊥ρ ⟦k⟧) ($-symbolic-names $) Γ #f #t))
      (σₖ⊕! Σ αₖ κ)
      {set (-ς↑ αₖ)}))

  (: app/rest/unsafe : ℓ -W¹ (Listof -W¹) -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  ;; Apply function with (in general, part of) rest arguments already allocated,
  ;; assuming that init/rest args are already checked to be compatible.
  (define (app/rest/unsafe ℓ W-func W-inits W-rest $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ V-func t-func) W-func)
    (define num-inits (length W-inits))

    ;; Attach trivial symbol to value
    (define (V->W¹ [V : -V]) (-W¹ V #f))

    (: app-prim/rest : -o → (℘ -ς))
    (define (app-prim/rest o)
      (for/union : (℘ -ς) ([V-rests (in-set (unalloc σ (-W¹-V W-rest)))] #:when V-rests)
        (app ℓ W-func (append W-inits (map V->W¹ V-rests)) $ Γ ⟪ℋ⟫ Σ ⟦k⟧)))

    (: app-clo/rest : -formals -⟦e⟧ -ρ -Γ → (℘ -ς))
    (define (app-clo/rest xs ⟦e⟧ ρₕ Γₕ)
      (match xs
        ;; TODO: if we assume clo as rest-arg, this path may never be reached...
        [(? list? xs)
         (define n (length xs))
         (define num-remaining-inits (- n num-inits))
         (for/union : (℘ -ς) ([V-rests (in-set (unalloc σ (-W¹-V W-rest)))]
                              #:when V-rests
                              #:when (= (length V-rests) num-remaining-inits))
           ((app-clo xs ⟦e⟧ ρₕ Γₕ t-func)
            ℓ (append W-inits (map V->W¹ V-rests)) $ Γ ⟪ℋ⟫ Σ ⟦k⟧))]
        [(-var zs z)
         (define n (length zs))
         (define num-remaining-inits (- n num-inits))
         (define-values (⟪ℋ⟫ₑₑ looped?) (⟪ℋ⟫+ ⟪ℋ⟫ (-edge ⟦e⟧ ℓ)))
         (define ρₕ.dom (dom ρₕ))
         (define unsure-locs (unsure-locations ρₕ.dom (-λ? t-func) looped?))
         (define $₀ (if looped? ($-del* ($-del* $ unsure-locs) (bound-vars ⟦e⟧)) ($-del* $ unsure-locs))) ; FIXME do it properly

         (: app/adjusted-args! : (Listof -W¹) -W¹ → -ς)
         (define (app/adjusted-args! W-inits W-rest)
           (define-values (ρₕ₀ $₁) (alloc-init-args! Σ $₀ Γ ρₕ ⟪ℋ⟫ₑₑ zs W-inits looped?))
           (define αᵣ (-α->⟪α⟫ (-α.x z ⟪ℋ⟫ₑₑ)))
           (σ⊕V! Σ αᵣ (-W¹-V W-rest))
           (define ρₕ* (ρ+ ρₕ₀ z αᵣ))
           (define $* ($-set $₁ z (-W¹-t W-rest)))
           (define Γₕ* (if looped? Γₕ (copy-Γ ($-symbolic-names $*) Γₕ Γ)))
           (define $**
             (let ([root (∪ (ρ->⟪α⟫s ρₕ*) (⟦k⟧->⟪α⟫s ⟦k⟧ (-Σ-σₖ Σ)))])
               ($-cleanup (gc-$ $* σ root))))
           (define αₖ (-ℬ $** ⟪ℋ⟫ₑₑ xs ⟦e⟧ ρₕ* Γₕ))
           (define κ
             (let* ([δ$ ($-extract $ (cons z zs))]
                    [⟦k⟧* (invalidate-$∷ unsure-locs (restore-$∷ δ$ (restore-ctx∷ ⟪ℋ⟫ ⟦k⟧)))])
               (-κ.rt ⟦k⟧* ($-symbolic-names $) Γ #f looped?)))
           (σₖ⊕! Σ αₖ κ)
           (-ς↑ αₖ))
         
         (cond
           ;; Need to retrieve some more arguments from `W-rest` as part of inits
           [(<= 0 num-remaining-inits)
            (for/set: : (℘ -ς) ([V-unalloc (in-set (unalloc-prefix σ (-W¹-V W-rest) num-remaining-inits))])
              (match-define (cons V-inits-more V-rest*) V-unalloc)
              (define W-inits* (append W-inits (map V->W¹ V-inits-more)))
              (app/adjusted-args! W-inits* (-W¹ V-rest* #f)))]
           ;; Need to allocate some init arguments as part of rest-args
           [else
            (define-values (W-inits* W-inits.rest) (split-at W-inits n))
            (define V-rest* (alloc-rest-args! Σ Γ ⟪ℋ⟫ₑₑ ℓ W-inits.rest #:end (-W¹-V W-rest)))
            {set (app/adjusted-args! W-inits* (-W¹ V-rest* #f))}])]))

    (: app-Ar/rest : -=>_ ⟪α⟫ -l³ → (℘ -ς))
    (define (app-Ar/rest C α l³)
      (match C
        [(-=> (-var αℓs₀ (-⟪α⟫ℓ αᵣ ℓᵣ)) (-⟪α⟫ℓ β ℓₐ) _)
         (define n (length αℓs₀))
         (define num-remaining-inits (- n num-inits))
         (cond
           ;; Need to retrieve some more arguments from `W-rest` as part of inits
           [(<= 0 num-remaining-inits)
            (for*/union : (℘ -ς) ([Vᵤ (in-set (σ@ Σ α))]
                                 [unalloced (in-set (unalloc-prefix σ (-W¹-V W-rest) num-remaining-inits))])
              (match-define (cons V-inits-more V-rest*) unalloced)
              (define W-inits* (append W-inits (map V->W¹ V-inits-more)))
              (define W-rest* (-W¹ V-rest* #f))
              ((apply-app-Ar C #f Vᵤ t-func l³) ℓ W-inits* W-rest* Γ ⟪ℋ⟫ Σ ⟦k⟧))]
           ;; Need to allocate some init arguments as part of rest-args
           [else
            (define-values (W-inits* W-inits.rest) (split-at W-inits n))
            (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ (-edge #|HACK|# (mk-rt (-W¹ C #f)) ℓ)))
            (define V-rest* (alloc-rest-args! Σ Γ ⟪ℋ⟫ₑₑ ℓ W-inits.rest #:end (-W¹-V W-rest)))
            (define W-rest* (-W¹ V-rest* #f))
            (for/union : (℘ -ς) ([Vᵤ (in-set (σ@ Σ α))])
                       ((apply-app-Ar C #f Vᵤ t-func l³) ℓ W-inits* W-rest* Γ ⟪ℋ⟫ Σ ⟦k⟧))])]
        [_
         (error 'app-Ar/rest "TODO: `apply` for function wrapped in ~a" (show-V C))]))
    
    (match V-func
      [(-Clo xs ⟦e⟧ ρₕ Γₕ) (app-clo/rest xs ⟦e⟧ ρₕ Γₕ)]
      [(-Case-Clo clauses _ _) (error 'app/rest "TODO: case-lambda")]
      [(-Ar C α l³) (app-Ar/rest C α l³)]
      [(? -o? o) (app-prim/rest o)]
      [_ (error 'app/rest "unhandled: ~a" (show-W¹ W-func))]))

  (: unsure-locations : (℘ -loc) Boolean Boolean → (℘ -loc))
  (define (unsure-locations ls fv-same? looped?)
    (cond
      [(and fv-same? looped?)
       (for/set: : (℘ -loc) ([l (in-set ls)]
                             #:when (or (symbol? l) (-𝒾? l))
                             #:when (assignable? l))
         l)]
      [fv-same? ∅]
      [else ls]))

  ;; FIXME Duplicate macros
  (define-simple-macro (with-Γ+/-oW (σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
    (Γ+/-oW/handler on-t on-f σ Γ o W ...))
  )
