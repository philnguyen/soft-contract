#lang typed/racket/base

(provide app mon)

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "../delta.rkt"
         "base.rkt"
         racket/set
         racket/match)

(: app : -l -ℓ -W¹ (Listof -W¹) -Γ -𝒞 -σ -M -⟦k⟧ → (Values (℘ -ς) -Δσ -Δσₖ -ΔM))
(define (app l ℓ Wₕ Wₓs Γ 𝒞 σ M ⟦k⟧)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ
    (let ([sₕ* (match Vₕ
                 [(? -o? o) o]
                 [(-Ar _ (-α.def (-𝒾 o 'Λ)) _) o]
                 [(-Ar _ (-α.wrp (-𝒾 o 'Λ)) _) o]
                 [_ sₕ])])
      (apply -?@ sₕ* sₓs)))

  (define (app-st-p [s : -struct-info])
    (define A
      (case (MΓ⊢oW M Γ (-st-p s) (car Wₓs))
        [(✓) -True/Vs]
        [(✗) -False/Vs]
        [(?) -Bool/Vs]))
    (⟦k⟧ (-W A sₐ) Γ 𝒞 σ M))

  (define (app-st-mk [s : -struct-info])
    (define 𝒾 (-struct-info-id s))
    (define αs : (Listof -α.fld)
      (for/list ([i : Natural (-struct-info-arity s)])
        (-α.fld 𝒾 ℓ 𝒞 i)))
    (define-values (σ* δσ)
      (for/fold ([σ : -σ σ] [δσ : -Δσ ⊥σ])
                ([α αs] [Vₓ Vₓs])
        (values (σ⊔ σ  α Vₓ #t)
                (σ⊔ δσ α Vₓ #t))))
    (define V (-St s αs))
    (with-δσ δσ
      (⟦k⟧ (-W (list V) sₐ) Γ 𝒞 σ* M)))

  ;; Apply accessor
  (define (app-st-ac [s : -struct-info] [i : Natural])
    (define n (-struct-info-arity s))
    (match-define (list (and Wₓ (-W¹ Vₓ sₓ))) Wₓs)
    (define ac (-st-ac s i))
    (define p  (-st-p s))

    (define (blm) (-blm l (show-o ac) (list p) (list Vₓ)))

    (match Vₓ
      [(-St (== s) αs)
       (define α (list-ref αs i))
       (define-values (Vs _) (σ@ σ α))
       (for*/ans ([V Vs])
         (⟦k⟧ (-W (list V) sₐ) Γ 𝒞 σ M))]
      [(-St* (== s) αs α l³)
       (match-define (-l³ _ _ lₒ) l³)
       (define Ac (-W¹ ac ac))
       (cond
         ;; field is wrapped
         [(list-ref αs i) =>
          (λ ([αᵢ : -α])
            (define (Cᵢs _) (σ@ σ αᵢ))
            (error 'app-st-ac "TODO: wrapped mutable field"))]
         ;; field is unwrapped because it's immutable
         [else
          (define-values (Vₓ*s _) (σ@ σ α))
          (for*/ans ([Vₓ* Vₓ*s]) ;; TODO: could this loop forever due to cycle?
            (app lₒ ℓ Ac (list (-W¹ Vₓ* sₓ)) Γ 𝒞 σ M ⟦k⟧))])]
      [(-● _)
       (define-values (Γₒₖ Γₑᵣ) (Γ+/-W∋Ws M Γ (-W¹ p p) Wₓ))
       (⊕ (with-Γ Γₒₖ (⟦k⟧ (-W -●/Vs sₐ) Γₒₖ 𝒞 σ M))
          (with-Γ Γₑᵣ (⟦k⟧ (blm) Γₑᵣ 𝒞 σ M)))]
      [_ (⟦k⟧ (blm) Γ 𝒞 σ M)]))

  (define (app-st-mut [s : -struct-info] [i : Natural])
    (match-define (list Wₛ Wᵤ) Wₓs)
    (match-define (-W¹ Vₛ sₛ) Wₛ)
    (match-define (-W¹ Vᵤ _ ) Wᵤ)
    (define mut (-st-mut s i))
    (define p (-st-p s))

    (define (blm) (-blm l (show-o mut) (list p) (list Vₛ)))
    
    (match Vₛ
      [(-St (== s) αs)
       (define α (list-ref αs i))
       (define σ* (σ⊔ σ  α Vᵤ #f))
       (define-values (ςs δσ₀ δσₖ δM) (⟦k⟧ -Void/W Γ 𝒞 σ* M))
       (values ςs (σ⊔ δσ₀ α Vᵤ #f) δσₖ δM)]
      [(-St* (== s) αs α l³)
       (error 'app-st-mut "TODO")]
      [(-● _)
       (error 'app-st-mut "TODO")]
      [_ (⟦k⟧ (blm) Γ 𝒞 σ M)]))

  (define (app-unsafe-struct-ref)
    (error 'app-unsafe-struct-ref "TODO"))

  (define (app-unsafe-struct-set!)
    (error 'app-unsafe-struct-set! "TODO"))

  (define (app-vector-ref)
    (error 'app-vector-ref "TODO"))

  (define (app-vector-set!)
    (error 'app-vector-set! "TODO"))

  (define (app-contract-first-order-passes?)
    (error 'app-contract-first-order-passes? "TODO"))

  (define (app-δ [o : Symbol])
    (define-values (?Vs δσ) (δ 𝒞 ℓ M σ Γ o Wₓs))
    (cond [?Vs
           (with-δσ δσ
             (⟦k⟧ (-W ?Vs sₐ) Γ 𝒞 (⊔σ σ δσ) M))]
          [else (⊥ans)]))

  (define (app-clo [xs : -formals] [⟦e⟧ : -⟦e⟧] [ρₕ : -ρ] [Γₕ : -Γ])
    (define 𝒞* (𝒞+ 𝒞 (cons ⟦e⟧ ℓ)))
    (cond
      [(pair? xs)
       (define-values (δσ ρ*)
         (for/fold ([δσ : -Δσ ⊥σ] [ρ : -ρ ρₕ]) ([x xs] [Vₓ Vₓs])
           (define α (-α.x x 𝒞*))
           (values (σ⊔ δσ α Vₓ #t) (ρ+ ρ x α))))
       (define bnd
         (-binding (and sₕ (e->φ sₕ))
                   xs
                   (for/hash : (HashTable Var-Name -φ) ([x xs] [sₓ sₓs] #:when sₓ)
                     (values x (e->φ sₓ)))))
       (define αₖ (-ℬ ⟦e⟧ ρ*))
       (define κ (-κ ⟦k⟧ Γ 𝒞 bnd))
       (define δσₖ (hash αₖ {set κ}))
       (values {set (-ς↑ αₖ Γₕ 𝒞*)} δσ δσₖ ⊥M)]
      [else (error 'app-clo "TODO: varargs")]))
  
  (match Vₕ
    ;; Struct operators cannot be handled by `δ`, because structs can be arbitrarily wrapped
    ;; by proxies, and contract checking is arbitrarily deep
    ;; Also, there's no need to check for preconditions, because they should have been caught
    ;; by wrapping contracts
    [(-st-p  s) (app-st-p  s)]
    [(-st-mk s) (app-st-mk s)]
    [(-st-ac  s i) (app-st-ac  s i)]
    [(-st-mut s i) (app-st-mut s i)]
    ['contract-first-order-passes? (app-contract-first-order-passes?)]
    ['vector-ref (app-vector-ref)]
    ['vector-set! (app-vector-set!)]
    ['unsafe-struct-ref  (app-unsafe-struct-ref)]
    ['unsafe-struct-set! (app-unsafe-struct-set!)]

    ;; Regular stuff
    [(? symbol? o) (app-δ o)]
    [(-Clo xs ⟦e⟧ ρₕ Γₕ)
     (app-clo xs ⟦e⟧ ρₕ Γₕ)]
    [_ (error 'app "TODO: ~a" (show-V Vₕ))]))

(: mon : -l³ -ℓ -W¹ -W¹ -Γ -𝒞 -σ -M -⟦k⟧ → (Values (℘ -ς) -Δσ -Δσₖ -ΔM))
(define (mon l³ ℓ W-C W-V Γ 𝒞 σ M ⟦k⟧)
  (error 'mon "TODO"))
