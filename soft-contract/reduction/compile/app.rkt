#lang typed/racket/base

(provide app mon)

(require "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt"
         "../delta.rkt"
         "utils.rkt"
         "base.rkt"
         racket/set
         racket/match)

(: app : -l -ℓ -W¹ (Listof -W¹) -Γ -𝒞 -Σ -⟦k⟧! → (℘ -ς))
(define (app l ℓ Wₕ Wₓs Γ 𝒞 Σ ⟦k⟧)
  (match-define (-Σ σ σₖ M) Σ)
  (match-define (-W¹ Vₕ sₕ) Wₕ)
  (define-values (Vₓs sₓs) (unzip-by -W¹-V -W¹-s Wₓs))
  (define sₐ
    (let ([sₕ* (match Vₕ
                 [(? -o? o) o]
                 [(-Ar _ (-α.def (-𝒾 o 'Λ)) _) o]
                 [(-Ar _ (-α.wrp (-𝒾 o 'Λ)) _) o]
                 [_ sₕ])])
      (apply -?@ sₕ* sₓs)))

  (: blm-arity : Arity Natural → -blm)
  (define (blm-arity required provided)
    ;; HACK for error message. Probably no need to fix
    (define msg : Symbol
      (cond
        [sₕ (format-symbol "~a requires ~a arguments" (format "~a" (show-e sₕ)) required)]
        [else (format-symbol "require ~a arguments" required)]))
    (-blm l 'Λ (list msg) Vₓs))

  (define-syntax-rule (with-guarded-arity a* e ...)
    (let ([n (length Wₓs)]
          [a a*])
      (cond
        [(arity-includes? a n) e ...]
        [else (⟦k⟧ (blm-arity a n) Γ 𝒞 Σ)])))

  (define (app-st-p [s : -struct-info])
    (define A
      (case (MΓ⊢oW M Γ (-st-p s) (car Wₓs))
        [(✓) -True/Vs]
        [(✗) -False/Vs]
        [(?) -Bool/Vs]))
    (⟦k⟧ (-W A sₐ) Γ 𝒞 Σ))

  (define (app-st-mk [s : -struct-info])
    (define 𝒾 (-struct-info-id s))
    (define αs : (Listof -α.fld)
      (for/list ([i : Natural (-struct-info-arity s)])
        (-α.fld 𝒾 ℓ 𝒞 i)))
    (for ([α αs] [Vₓ Vₓs])
      (σ⊔! σ α Vₓ #t))
    (define V (-St s αs))
    (⟦k⟧ (-W (list V) sₐ) Γ 𝒞 Σ))

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
       (for/union : (℘ -ς) ([V Vs])
         (⟦k⟧ (-W (list V) sₐ) Γ 𝒞 Σ))]
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
          (for/union : (℘ -ς) ([Vₓ* Vₓ*s]) ;; TODO: could this loop forever due to cycle?
            (app lₒ ℓ Ac (list (-W¹ Vₓ* sₓ)) Γ 𝒞 Σ ⟦k⟧))])]
      [(-● _)
       (with-Γ+/- ([(Γₒₖ Γₑᵣ) (Γ+/-W∋Ws M Γ (-W¹ p p) Wₓ)])
         #:true  (⟦k⟧ (-W -●/Vs sₐ) Γₒₖ 𝒞 Σ)
         #:false (⟦k⟧ (blm) Γₑᵣ 𝒞 Σ))]
      [_ (⟦k⟧ (blm) Γ 𝒞 Σ)]))

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
       (σ⊔! σ α Vᵤ #f)
       (⟦k⟧ -Void/W Γ 𝒞 Σ)]
      [(-St* (== s) αs α l³)
       (error 'app-st-mut "TODO")]
      [(-● _)
       (error 'app-st-mut "TODO")]
      [_ (⟦k⟧ (blm) Γ 𝒞 Σ)]))

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
    (define ?Vs (δ! 𝒞 ℓ M σ Γ o Wₓs))
    (cond [?Vs (⟦k⟧ (-W ?Vs sₐ) Γ 𝒞 Σ)]
          [else ∅]))

  (define (app-clo [xs : -formals] [⟦e⟧ : -⟦e⟧!] [ρₕ : -ρ] [Γₕ : -Γ])
    (define 𝒞* (𝒞+ 𝒞 (cons ⟦e⟧ ℓ)))
    (cond
      [(pair? xs)
       (define ρ* ; with side effects widening store
         (for/fold ([ρ : -ρ ρₕ]) ([x xs] [Vₓ Vₓs])
           (define α (-α.x x 𝒞*))
           (σ⊔! σ α Vₓ #t)
           (ρ+ ρ x α)))
       (define bnd
         (-binding sₕ
                   xs
                   (for/hasheq : (HashTable Var-Name -s) ([x xs] [sₓ sₓs] #:when sₓ)
                     (values x sₓ))))
       (define αₖ (-ℬ ⟦e⟧ ρ*))
       (define κ (-κ ⟦k⟧ Γ 𝒞 bnd))
       (⊔! σₖ αₖ κ)
       {set (-ς↑ αₖ Γₕ 𝒞*)}]
      [else (error 'app-clo "TODO: varargs")]))

  (define (app-And/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
    (app l ℓ W₁ Wₓs Γ 𝒞 Σ (and/c∷ l ℓ W₂ (car Wₓs) ⟦k⟧)))

  (define (app-Or/C [W₁ : -W¹] [W₂ : -W¹]) : (℘ -ς)
    (app l ℓ W₁ Wₓs Γ 𝒞 Σ (or/c∷ l ℓ W₂ (car Wₓs) ⟦k⟧)))
  
  (define (app-Not/C [Wᵤ : -W¹]) : (℘ -ς)
    (app l ℓ Wᵤ Wₓs Γ 𝒞 Σ (not/c∷ l ⟦k⟧)))

  (define (app-St/C [s : -struct-info] [Ws : (Listof -W¹)]) : (℘ -ς)
    (match-define (list Wₓ) Wₓs)
    (match-define (-W¹ Vₓ _) Wₓ)
    (match Vₓ
      [(or (-St (== s) _) (-St* (== s) _ _ _))
       (error 'app-St/C "TODO")]
      [_
       (⟦k⟧ -False/W Γ 𝒞 Σ)]))

  (define (app-Ar [C : -V] [Vᵤ : -V] [l³ : -l³]) : (℘ -ς)
    (error 'app-Ar "TODO"))

  (define (app-Indy [C : -V] [Vᵤ : -V] [l³ : -l³]) : (℘ -ς)
    (error 'app-Indy "TODO"))

  (define (app-Case [C : -V] [Vᵤ : -V] [l³ : -l³]) : (℘ -ς)
    (error 'app-Case "TODO"))

  (define (app-opq) : (℘ -ς)
    (define Wₕᵥ
      (let-values ([(Vs _) (σ@ σ (-α.def havoc-𝒾))])
        (assert (= 1 (set-count Vs)))
        (-W¹ (set-first Vs) havoc-𝒾)))
    (for/fold ([ac : (℘ -ς) (⟦k⟧ (-W -●/Vs sₐ) Γ 𝒞 Σ)])
              ([Wₓ Wₓs])
      (app 'Λ ℓ Wₕᵥ (list Wₓ) Γ 𝒞 Σ ⟦k⟧)))
  
  (match Vₕ
    ;; Struct operators cannot be handled by `δ`, because structs can be arbitrarily wrapped
    ;; by proxies, and contract checking is arbitrarily deep
    ;; Also, there's no need to check for preconditions, because they should have been caught
    ;; by wrapping contracts
    [(-st-p  s) (app-st-p  s)]
    [(-st-mk s) (app-st-mk s)]
    [(-st-ac  s i) (with-guarded-arity 1 (app-st-ac  s i))]
    [(-st-mut s i) (with-guarded-arity 2 (app-st-mut s i))]
    ['contract-first-order-passes? (app-contract-first-order-passes?)]
    ['vector-ref (app-vector-ref)]
    ['vector-set! (app-vector-set!)]
    ['unsafe-struct-ref  (app-unsafe-struct-ref)]
    ['unsafe-struct-set! (app-unsafe-struct-set!)]

    ;; Regular stuff
    [(? symbol? o) (app-δ o)]
    [(-Clo xs ⟦e⟧ ρₕ Γₕ)
     (with-guarded-arity (formals-arity xs)
       (app-clo xs ⟦e⟧ ρₕ Γₕ))]
    [(-Case-Clo clauses ρ Γ)
     (error 'app "TODO: case-lambda")]
    [(-Ar C α l³)
     (with-guarded-arity (guard-arity C)
       (cond
         [(-=>? C)  (for/union : (℘ -ς) ([Vᵤ (σ@ᵥ σ α)]) (app-Ar   C Vᵤ l³))]
         [(-=>i? C) (for/union : (℘ -ς) ([Vᵤ (σ@ᵥ σ α)]) (app-Indy C Vᵤ l³))]
         [else      (for/union : (℘ -ς) ([Vᵤ (σ@ᵥ σ α)]) (app-Case C Vᵤ l³))]))]
    [(-And/C #t α₁ α₂)
     (with-guarded-arity 1
       (define-values (c₁ c₂)
         (match-let ([(list s₁ s₂) (-app-split sₕ 'and/c 2)])
           (values (or s₁ (and (-e? α₁) α₁))
                   (or s₂ (and (-e? α₂) α₂)))))
       (for*/union : (℘ -ς) ([C₁ (σ@ᵥ σ α₁)] [C₂ (σ@ᵥ σ α₂)])
         (app-And/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
    [(-Or/C #t α₁ α₂)
     (with-guarded-arity 1
       (define-values (c₁ c₂)
         (match-let ([(list s₁ s₂) (-app-split sₕ 'or/c 2)])
           (values (or s₁ (and (-e? α₁) α₁))
                   (or s₂ (and (-e? α₂) α₂)))))
       (for*/union : (℘ -ς) ([C₁ (σ@ᵥ σ α₁)] [C₂ (σ@ᵥ σ α₂)])
         (app-Or/C (-W¹ C₁ c₁) (-W¹ C₂ c₂))))]
    [(-Not/C α)
     (with-guarded-arity 1
       (define c*
         (match-let ([(list s) (-app-split sₕ 'not/c 1)])
           (or s (and (-e? α) α))))
       (for/union : (℘ -ς) ([C* (σ@ᵥ σ α)])
         (app-Not/C (-W¹ C* c*))))]
    [(-St/C #t s αs)
     (with-guarded-arity 1
       (define cs : (Listof -s)
         (for/list ([s (-struct/c-split sₕ (-struct-info-arity s))]
                    [α αs])
           (or s (and (-e? α) α))))
       (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
         (app-St/C s (map -W¹ Cs cs))))]
    [(-● _)
     (case (MΓ⊢oW M Γ 'procedure? Wₕ)
       [(✓ ?) (app-opq)]
       [(✗) (⟦k⟧ (-blm l 'Λ (list 'procedure?) (list Vₕ)) Γ 𝒞 Σ)])]
    [_ (error 'app "TODO: ~a" (show-V Vₕ))]))

(: mon : -l³ -ℓ -W¹ -W¹ -Γ -𝒞 -Σ -⟦k⟧! → (℘ -ς))
(define (mon l³ ℓ W-C W-V Γ 𝒞 Σ ⟦k⟧)
  (error 'mon "TODO"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/memo (not/c∷ [l : -l] [⟦k⟧! : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧! A Γ 𝒞 Σ)
    (match-define (-W Vs v) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V v)])
         #:true  (⟦k⟧! -False/W Γ₁ 𝒞 Σ)
         #:false (⟦k⟧! -True/W  Γ₂ 𝒞 Σ))]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs))
       (⟦k⟧! blm Γ 𝒞 Σ)])))

(define/memo (and/c∷ [l : -l] [ℓ : -ℓ] [Wᵣ : -W¹] [Wₓ : -W¹] [⟦k⟧! : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧! A Γ 𝒞 Σ)
    (match-define (-W Vs v) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V v)])
         #:true  (app l ℓ Wᵣ (list Wₓ) Γ 𝒞 Σ ⟦k⟧!)
         #:false (⟦k⟧! -False/W Γ₂ 𝒞 Σ))]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs))
       (⟦k⟧! blm Γ 𝒞 Σ)])))

(define/memo (or/c∷ [l : -l] [ℓ : -ℓ] [Wᵣ : -W¹] [Wₓ : -W¹] [⟦k⟧! : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧! A Γ 𝒞 Σ)
    (match-define (-W Vs v) A)
    (match Vs
      [(list V)
       (with-Γ+/- ([(Γ₁ Γ₂) (Γ+/-V (-Σ-M Σ) Γ V v)])
         #:true  (⟦k⟧! A Γ₁ 𝒞 Σ)
         #:false (app l ℓ Wᵣ (list Wₓ) Γ₂ 𝒞 Σ ⟦k⟧!))]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs))
       (⟦k⟧! blm Γ 𝒞 Σ)])))

(define/memo (st/c∷ [l : -l]
                    [ℓ : -ℓ]
                    [Wᵢs : (Listof -W¹)]
                    [Wᵥs : (Listof -W¹)]
                    [⟦k⟧! : -⟦k⟧!]) : -⟦k⟧!
  (with-error-handling (⟦k⟧! A Γ 𝒞 Σ)
    (match-define (-W Vs v) A)
    (match Vs
      [(list V)
       (match* (Wᵢs Wᵥs)
         [('() '())
          (error 'st/c "TODO")]
         [((cons Wᵢ Wᵢs) (cons Wᵥ Wᵥs))
          (error 'st/c "TODO")])]
      [_
       (define blm (-blm l 'Λ '(|1 value|) Vs))
       (⟦k⟧! blm Γ 𝒞 Σ)])))
