#lang racket/base

(require racket/set racket/list racket/match redex
         "lib.rkt" "syntax.rkt" "proof-relation.rkt" "delta.rkt")

;; Load expression into initial program configuration
(define-metafunction λ-sym
  𝑰 : e -> (ς σ Ξ M)
  [(𝑰 e) (((e ⊥ρ) ⊤Γ (τ)) ⊥σ ⊥Ξ ⊥M)
   (where τ (->τ e ⊥ρ ⊤Γ))])

;; Narrow reduction step
(define ->₁
  (reduction-relation
   λ-sym #:domain (ς σ Ξ M)
   
   [--> (((x ρ)   Γ κ) σ Ξ M)
        (((V @ S) Γ κ) σ Ξ M)
        Var
        (judgment-holds (∈ V (σ@ σ (ρ@ ρ x))))
        (where S (canonicalize Γ x))
        (where #f (spurious? M Γ V S))]

   ;; Value
   [--> (((b _)   Γ κ) σ Ξ M)
        (((b @ b) Γ κ) σ Ξ M)
        Base]
   [--> ((((λ (x) e) ρ)                                 Γ κ) σ Ξ M)
        ((((Clo x e ρ (invalidate-muts Γ)) @ (λ (x) e)) Γ κ) σ Ξ M)
        Lam]
   [--> (((• ρ)   Γ κ) σ Ξ M)
        (((● @ •) Γ κ) σ Ξ M)
        Opq]

   ;; Set!
   [--> ((((set! x e) ρ) Γ (                  φ ... τ)) σ Ξ M)
        (((e ρ)          Γ ((set! x (ρ@ ρ x)) φ ... τ)) σ Ξ M)
        Set!-Push]
   [--> (((V @ S) Γ   ((set! x α) φ ... τ)) σ   Ξ M)
        (((1 @ 1) Γ_1 (           φ ... τ)) σ_1 Ξ M) ; `1` as `void`
        Set!-Pop
        (where Γ_1 (bind Γ x S))
        (where σ_1 (⊔ σ α V))]

   ;; Conditional
   [--> ((((if e e_1 e_2) ρ) Γ (               φ ... τ)) σ Ξ M)
        ((  (   e         ρ) Γ ((if e_1 e_2 ρ) φ ... τ)) σ Ξ M)
        If-Push]
   [--> (((V @ S) Γ   ((if e _ ρ) φ ... τ)) σ Ξ M)
        (((e ρ)   Γ_t (           φ ... τ)) σ Ξ M)
        If-True
        (where (Γ_t _) (MΓ+/- M Γ V S))]
   [--> (((V @ S) Γ   ((if _ e ρ) φ ... τ)) σ Ξ M)
        (((e ρ)   Γ_f (           φ ... τ)) σ Ξ M)
        If-False
        (where (_ Γ_f) (MΓ+/- M Γ V S))]

   ;; Application
   [--> ((((e_f e_x l) ρ) Γ (          φ ... τ)) σ Ξ M)
        (((e_f ρ)         Γ ((e_x ρ l) φ ... τ)) σ Ξ M)
        App-Push]
   [--> ((W     Γ  ((e ρ l) φ ... τ)) σ Ξ M)
        (((e ρ) Γ  ((W l)   φ ... τ)) σ Ξ M)
        App-Swap]
   [--> ((W_x      Γ   ((W_f l) φ ... τ)) σ   Ξ   M)
        (((e ρ_f*) Γ_f (            τ_1)) σ_1 Ξ_1 M)
        β
        (where ((Clo x e ρ_f Γ_f) @ S_f) W_f)
        (where (V_x @ S_x) W_x)
        (where α (->α x e S_x ,(Γ-props (term Γ))))
        (where σ_1 (⊔ σ α V_x))
        (where ρ_f* ,(hash-set (term ρ_f) (term x) (term α)))
        (where τ_1 (->τ e ρ_f* Γ_f))
        (where Ξ_1 (⊔ Ξ τ_1 ((rt Γ S_f [x ↦ S_x]) φ ... τ)))]
   [--> ((W_x Γ   ((W_f l) φ ... τ)) σ Ξ M)
        ((A   Γ_a (        φ ... τ)) σ Ξ M)
        δ
        (where (o @ _) W_f)
        (where (Γ_a A) (δ l M Γ o W_x))]
   [--> ((W_x                        Γ   ((W l) _ ... τ)) σ Ξ M)
        (((blame l "apply non-proc") Γ_1 (            τ)) σ Ξ M)
        App-Err
        (where (_ Γ_1) (MΓ+/-oW M Γ procedure? W))]
   [--> ((W_x     Γ   ((W_f l)                  φ ... τ)) σ Ξ M)
        (((0 @ 0) Γ_1 ((havoc W_x (@S S_f S_x)) φ ... τ)) σ Ξ M)
        App-●
        (where (● @ S_f) W_f)
        (where (_ @ S_x) W_x)
        (where (Γ_1 _) (MΓ+/-oW M Γ procedure? W_f))]

   ;; Havoc
   [--> ((_       Γ ((havoc W S) φ ... τ)) σ Ξ M)
        (((● @ S) Γ (            φ ... τ)) σ Ξ M) ; assume opaque function is extensional by default
        Havoc-Done]
   [--> ((_        Γ (          (havoc W S) φ ... τ)) σ Ξ M)
        (((● @ #f) Γ ((W ℓ•) (havoc W S) φ ... τ)) σ Ξ M)
        Havoc-Cont]

   ;; Return + Change context
   ;; TODO: throw away spurious returns (where path conditions disagree)
   [--> (((V  @ S  ) Γ    (        τ)) σ Ξ M  )
        (((V  @ S_a) Γ_0* (φ ... τ_0)) σ Ξ M_1)
        Rt
        (judgment-holds (∈ ((rt Γ_0 S_f [x ↦ S_x]) φ ... τ_0) (Ξ@ Ξ τ)))
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
  (define ςs (map first (apply-reduction-relation* -> (term (𝑰 ,e)) #:cache-all? #t)))
  (values ςs (unbox σ) (unbox Ξ) (unbox M)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(module+ test

  (define-term e₁
    (-let ([!x 42])
      (-begin
         (set! !x 43))
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
  )

