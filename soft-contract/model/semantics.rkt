#lang racket/base

(require racket/set racket/list racket/match redex
         "lib.rkt" "syntax.rkt" "proof-relation.rkt" "delta.rkt")

;; Load expression into initial program configuration
(define-metafunction λ-sym
  𝑰 : e -> (ς σ Ξ M)
  [(𝑰 e) (((e ⊥ρ) ⊤Γ (τ) (𝒸 0)) ⊥σ ⊥Ξ ⊥M)
   (where τ (->τ e ⊥ρ ⊤Γ))])

;; Narrow reduction step
(define ->₁
  (reduction-relation
   λ-sym #:domain (ς σ Ξ M)
   
   [--> (((x ρ)   Γ κ 𝒞) σ Ξ M)
        (((V @ S) Γ κ 𝒞) σ Ξ M)
        Var
        (judgment-holds (∈ V (σ@ σ (ρ@ ρ x))))
        (where S (canonicalize Γ x))
        (where #f (spurious? M Γ V S))]

   ;; Value
   [--> (((b _)   Γ κ 𝒞) σ Ξ M)
        (((b @ b) Γ κ 𝒞) σ Ξ M)
        Base]
   [--> ((((λ (x) e) ρ)                                 Γ κ 𝒞) σ Ξ M)
        ((((Clo x e ρ (invalidate-muts Γ)) @ (λ (x) e)) Γ κ 𝒞) σ Ξ M)
        Lam]
   [--> (((• ρ)   Γ κ 𝒞) σ Ξ M)
        (((● @ •) Γ κ 𝒞) σ Ξ M)
        Opq]

   ;; Set!
   [--> ((((set! x e) ρ) Γ (                  φ ... τ) 𝒞) σ Ξ M)
        (((e ρ)          Γ ((set! x (ρ@ ρ x)) φ ... τ) 𝒞) σ Ξ M)
        Set!-Push]
   [--> (((V @ S) Γ   ((set! x α) φ ... τ) 𝒞) σ   Ξ M)
        (((1 @ 1) Γ_1 (           φ ... τ) 𝒞) σ_1 Ξ M) ; `1` as `void`
        Set!-Pop
        (where Γ_1 (bind Γ x S))
        (where σ_1 (⊔ σ α V))]

   ;; Conditional
   [--> ((((if e e_1 e_2) ρ) Γ (               φ ... τ) 𝒞) σ Ξ M)
        ((  (   e         ρ) Γ ((if e_1 e_2 ρ) φ ... τ) 𝒞) σ Ξ M)
        If-Push]
   [--> (((V @ S) Γ   ((if e _ ρ) φ ... τ) 𝒞) σ Ξ M)
        (((e ρ)   Γ_t (           φ ... τ) 𝒞) σ Ξ M)
        If-True
        (where (Γ_t _) (MΓ+/- M Γ V S))]
   [--> (((V @ S) Γ   ((if _ e ρ) φ ... τ) 𝒞) σ Ξ M)
        (((e ρ)   Γ_f (           φ ... τ) 𝒞) σ Ξ M)
        If-False
        (where (_ Γ_f) (MΓ+/- M Γ V S))]

   ;; Application
   [--> ((((e_f e_x l) ρ) Γ (          φ ... τ) 𝒞) σ Ξ M)
        (((e_f ρ)         Γ ((e_x ρ l) φ ... τ) 𝒞) σ Ξ M)
        App-Push]
   [--> ((W     Γ  ((e ρ l) φ ... τ) 𝒞) σ Ξ M)
        (((e ρ) Γ  ((W l)   φ ... τ) 𝒞) σ Ξ M)
        App-Swap]
   [--> ((W_x      Γ   ((W_f l) φ ... τ) 𝒞  ) σ   Ξ   M)
        (((e ρ_f*) Γ_f (            τ_1) 𝒞_1) σ_1 Ξ_1 M)
        β
        (where ((Clo x e ρ_f Γ_f) @ S_f) W_f)
        (where (V_x @ S_x) W_x)
        (where 𝒞_1 (𝒞+ 𝒞 (e l)))
        (where α (->α x 𝒞_1))
        (where ρ_f* ,(hash-set (term ρ_f) (term x) (term α)))
        (where σ_1 (⊔ σ α V_x))
        (where τ_1 (->τ e ρ_f* Γ_f))
        (where Ξ_1 (⊔ Ξ τ_1 ((rt 𝒞 Γ S_f [x ↦ S_x]) φ ... τ)))
        ; Debug
        ;(where (𝒸 n_1) 𝒞_1)
        ;(where _ ,(printf "~a~n" (term n_1)))
        ]
   [--> ((W_x Γ   ((W_f l) φ ... τ) 𝒞) σ Ξ M)
        ((A   Γ_a (        φ ... τ) 𝒞) σ Ξ M)
        δ
        (where (o @ _) W_f)
        (where (Γ_a A) (δ l M Γ o W_x))]
   [--> ((W_x                        Γ   ((W l) _ ... τ) 𝒞) σ Ξ M)
        (((blame l "apply non-proc") Γ_1 (            τ) 𝒞) σ Ξ M)
        App-Err
        (where (_ Γ_1) (MΓ+/-oW M Γ procedure? W))]
   [--> ((W_x     Γ   ((W_f l)                  φ ... τ) 𝒞) σ Ξ M)
        (((0 @ 0) Γ_1 ((havoc W_x (@S S_f S_x)) φ ... τ) 𝒞) σ Ξ M)
        App-●
        (where (● @ S_f) W_f)
        (where (_ @ S_x) W_x)
        (where (Γ_1 _) (MΓ+/-oW M Γ procedure? W_f))]

   ;; Havoc
   [--> ((_       Γ ((havoc W S) φ ... τ) 𝒞) σ Ξ M)
        (((● @ S) Γ (            φ ... τ) 𝒞) σ Ξ M) ; assume opaque function is extensional by default
        Havoc-Done]
   [--> ((_        Γ (       (havoc W S) φ ... τ) 𝒞) σ Ξ M)
        (((● @ #f) Γ ((W ℓ•) (havoc W S) φ ... τ) 𝒞) σ Ξ M)
        Havoc-Cont]

   ;; Return + Change context
   ;; TODO: throw away spurious returns (where path conditions disagree)
   [--> (((V  @ S  ) Γ    (        τ) 𝒞  ) σ Ξ M  )
        (((V  @ S_a) Γ_0* (φ ... τ_0) 𝒞_0) σ Ξ M_1)
        Rt
        (judgment-holds (∈ ((rt 𝒞_0 Γ_0 S_f [x ↦ S_x]) φ ... τ_0) (Ξ@ Ξ τ)))
        (where S_a ,(and (term S) (term (@S S_f S_x))))
        (where Γ_0*
               ,(cond ; attach another path-condition "tail" if function was extensional
                  [(term S_a)
                   (make-Γ (Γ-canonical (term Γ_0))
                           (Γ-props (term Γ_0))
                           (set-add (Γ-rests (term Γ_0)) (term (τ S_f [x ↦ S_x]))))]
                  [else (term Γ_0)]))
        (where M_1 (⊔ M τ ,(make-Ans (term Γ) (term (V @ S)))))]
   
   ))

;; Widened reduction step. Return the relation as well as 3 (boxed) stores
(define (make-->)
  (let ([σ^ (box (hash))]
        [Ξ^ (box (hash))]
        [M^ (box (hash))])
    (values
     (reduction-relation
      λ-sym #:domain (ς σ Ξ M)
      [--> (ς σ Ξ M)
           (ς_1 σ_1* Ξ_1* M_1*)
           (computed-name (term any_name))
           (where (_ ... (any_name (ς_1 σ_1 Ξ_1 M_1)) _ ...)
                  ,(apply-reduction-relation/tag-with-names ->₁ (term (ς σ Ξ M))))
           (where σ_1* (⊔/m σ_1 ,(unbox σ^)))
           (where Ξ_1* (⊔/m Ξ_1 ,(unbox Ξ^)))
           (where M_1* (⊔/m M_1 ,(unbox M^)))
           (where _ ,(set-box! σ^ (term σ_1*)))
           (where _ ,(set-box! Ξ^ (term Ξ_1*)))
           (where _ ,(set-box! M^ (term M_1*)))])
     σ^
     Ξ^
     M^)))

;; Visualize program traces and return 3 (concurrently updated) global stores
(define (viz e)
  (define-values (-> σ Ξ M) (make-->))
  (traces -> (term (𝑰 ,e)))
  (values σ Ξ M))

;; Evaluate program and return answer as well as 3 global stores
(define (ev e) 
  (define-values (-> σ Ξ M) (make-->))
  (define ςs (remove-duplicates
              (map first (apply-reduction-relation* -> (term (𝑰 ,e)) #:cache-all? #t))))
  (values ςs (unbox σ) (unbox Ξ) (unbox M)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(module+ test

  (define-term e₁
    (-let ([!x 42])
       (set! !x 43)
       (add1 !x ℓ₁)))

  (define-term e₂
    (-let ([f •₀])
       (if (f 1 ℓ₀)
           (if (f 1 ℓ₁) 42 43) ; should reach 42 only
           (if (f 1 ℓ₂) 44 45)))) ; should reach 45 only

  (define-term e₃
    (-let ([!x 42])
      (-let ([f (λ (y) (set! !x (add1 !x ℓ₀)))])
         (•₁ f ℓ•))))

  (define-term e₄
    ((λ (f) ((f f ℓ₀) 0 ℓ₁))
     (λ (x) x)
     ℓ₂))

  (define-term e₅
    (-let* ([jd (λ (z) z)]
            [id (λ (u) (jd u ℓ₂))]
            [x (id 0 ℓ₀)]
            [y (id 1 ℓ₁)])
       y))

  (define-term e-kcfa3
    ((λ (f1)
       (-let ([a (f1 1 ℓ₁)])
         (f1 0 ℓ₂)))
     (λ (x1)
       ((λ (f2)
          (-let ([b (f2 1 ℓ₃)])
            (f2 0 ℓ₄)))
        (λ (x2)
          ((λ (f3)
             (-let ([c (f3 1 ℓ₄)])
               (f3 0 ℓ₅)))
           (λ (x3)
             ((λ (z) (((z x1 ℓ₆) x2 ℓ₇) x3 ℓ₈))
              (λ (y1)
                (λ (y2)
                  (λ (y3) y1)))
              ℓ₉))
           ℓ₁₀))
        ℓ₁₁))
     ℓ₁₂))

  (define-term e-sat-7
    (-let* ([try (λ (f) (-or (f 0 ℓ₀) (f 1 ℓ₁)))]
            [p (λ (x₁)
                  (λ (x₂)
                    (λ (x₃)
                      (λ (x₄)
                        (λ (x₅)
                          (λ (x₆)
                            (λ (x₇)
                              (-and x₁ x₂ x₃ x₄ x₅ x₆ x₇)
                              #;(-and (-or x₁ x₂)
                                    (-or x₁ (not x₂ ℓₙ₀) (not x₃ ℓₙ₁))
                                    (-or x₃ x₄)
                                    (-or (not x₄ ℓₙ₂) x₁)
                                    (-or (not x₂ ℓₙ₃) (not x₃ ℓₙ₄))
                                    (-or x₄ x₂))
                              )))))))]
            [solve
              (λ (q)
                (try (λ (n₁)
                       (try (λ (n₂)
                              (try (λ (n₃)
                                     (try (λ (n₄)
                                            (try (λ (n₅)
                                                   (try (λ (n₆)
                                                          (try (λ (n₇)
                                                                 (((((((q n₁ ℓ₀₁) n₂ ℓ₀₂) n₃ ℓ₀₃) n₄ ℓ₀₄) n₅ ℓ₀₅) n₆ ℓ₀₆) n₇ ℓ₀₇))
                                                               ℓ₁₇))
                                                        ℓ₁₆))
                                                 ℓ₁₅))
                                          ℓ₁₄))
                                   ℓ₁₃))
                            ℓ₁₂))
                     ℓ₁₁))])
       (solve p ℓₜ)))

  (define-term e-rep
    (-let* ([Y (λ (f)
                 (λ (x) (((λ (g) (f (λ (x) ((g g ℓY₀) x ℓY₁)) ℓY₂))
                          (λ (g) (f (λ (x) ((g g ℓY₃) x ℓY₄)) ℓY₅))
                          ℓY₆)
                         x
                         ℓY₇)))]
            [id (λ (a) a)]
            [mk-rep (λ (rep)
                      (λ (n)
                        (-let* ([id (λ (p) p)])
                           (if n
                               (add1 (rep (sub1 n ℓrep₁) ℓrep₂) ℓrep₃)
                               0))))])
      ((Y mk-rep ℓᵣ₀) 100 ℓᵣ₁)))

  ;; no letrec yet
  #;(define-term e-blur
    (-let* ([id (λ (x) x)]
            [blur (λ (y) y)]
            [lp (λ (a)
                  (λ (n)
                    (if n
                        (-let* ([r ((blur id ℓ₀) 1 ℓ₁)]
                                [s ((blur id ℓ₂) 0 ℓ₃)])
                          (not (((blur lp ℓ₄) s ℓ₅) (sub1 n ℓ₆) ℓ₇) ℓ₈))
                        (id a ℓ₉))))])
       ((lp 0 ℓ₁₀) 2 ℓ₁₁)))

  (define-term e-eta
    (-let* ([do-something (λ (z) 10)]
            [id (λ (y)
                  (-begin
                   (do-something 42 ℓ₄)
                   y))])
      ((id (λ (a) a) ℓ₀) 1 ℓ₁)
      ((id (λ (b) b) ℓ₂) 0 ℓ₃)))

  (define-term e-loop
    (-let* ([!lp1 2000]
            [a
             (set! !lp1
                   (λ (i)
                     (λ (x)
                       (-let ([a* (not i ℓ₁₄)])
                          (if
                           a*
                           x
                           (-let* ([!lp2 1000]
                                   [b
                                    (set! !lp2
                                          (λ (j)
                                            (λ (f)
                                              (λ (y)
                                                (-let ([b* (not j ℓ₁₃)])
                                                  (if b*
                                                      ((!lp1 (sub1 i ℓ₁₀) ℓ₁₁) y ℓ₁₂)
                                                      (-let ([tmp (f y ℓ₉)])
                                                        (((!lp2 (sub1 j ℓ₅) ℓ₆) f ℓ₇) tmp ℓ₈))))))))])
                             (((!lp2 10 ℓ₂) (λ (n) (add1 i ℓ₁₅)) ℓ₃) x ℓ₄)))))))])
      ((!lp1 10 ℓ₀) 0 ℓ₁)))

  (define-term e-mj09
    (-let* ([h (λ (b)
                 (-let* ([g (λ (z) z)]
                         [f (λ (k) (if b (k 1 ℓ₄) (k 2 ℓ₅)))]
                         [y (f (λ (x) x) ℓ₃)])
                   (g y ℓ₂)))]
            [x (h 1 ℓ₀)]
            [y (h 0 ℓ₁)])
      y))
  )

