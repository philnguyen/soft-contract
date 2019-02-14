#lang typed/racket/base

(provide hv@)

(require racket/set
         racket/list
         racket/match
         typed/racket/unit
         syntax/parse/define
         bnf
         set-extras
         unreachable
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         )

(define-unit hv@
  (import static-info^ meta-functions^
          sto^ cache^ val^
          exec^ app^)
  (export hv^)

  (define ● {set (-● ∅)})

  (: hv : Σ γ:hv → (Values R (℘ Err)))
  (define (hv Σ αₕᵥ)
    (ref-$! ($:Key:Hv Σ αₕᵥ)
            (λ ()
              (define-values (ΔΣ₁ es₁)
                (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ] [es : (℘ Err) ∅])
                          ([Vᵢ (in-set (unpack αₕᵥ Σ))])
                  (define-values (Vsᵢ ΔΣᵢ esᵢ) (do-hv Σ Vᵢ))
                  (values (ΔΣ⊔ ΔΣ (⧺ ΔΣᵢ (alloc αₕᵥ Vsᵢ)))
                          (∪ es esᵢ))))
              (define-values (r* es*) (hv (⧺ Σ ΔΣ₁) αₕᵥ))
              (match (collapse-R r*)
                [(cons _ ΔΣ*) (values (hash (ΔΣ⊔ ΔΣ₁ (⧺ ΔΣ₁ ΔΣ*)) {set (list ●)}) (∪ es₁ es*))]
                [#f (values (hash ΔΣ₁ {set (list ●)}) (∪ es₁ es*))]))))

  (: gen-havoc-expr : ((Listof -module) → E))
  (define (gen-havoc-expr ms)
    (define refs
      (for*/list : (Listof -x) ([m (in-list ms)]
                                [path (in-value (-module-path m))]
                                [form (in-list (-module-body m))] #:when (-provide? form)
                                [spec (in-list (-provide-specs form))] #:when (-p/c-item? spec))
        (match-define (-p/c-item x _ _) spec)
        (-x (-𝒾 x path) (loc->ℓ (loc 'top-level-havoc 0 0 (list x))))))
    (-@ (-•) refs (loc->ℓ (loc 'havoc-expr 0 0 '()))))

  (: do-hv : Σ V → (Values V^ ΔΣ (℘ Err)))
  ;; Havoc the value and collect behavioral values discovered
  (define (do-hv Σ V)
    (match V
      ;; Apply function to appropriate number of args
      [(or (? Clo?) (? Case-Clo?) (Guarded _ (? Fn/C?) _))
       (define on-arity : ((U Natural arity-at-least) → (Values V^ ΔΣ (℘ Err)))
         (match-lambda
           [(? index? k)
            (collapse Σ (app Σ (ℓ/tag 'app k) {set V} (make-list k ●)))]
           [(arity-at-least n)
            (define Vᵣ {set (-● {set 'list?})})
            (define W₀ (make-list n ●))
            (collapse Σ (app/rest Σ (ℓ/tag 'app 'varargs) {set V} W₀ Vᵣ))]))
       (match (arity-of V)
         [(? list? ks)
          (for/fold ([Vs : V^ ∅] [ΔΣ : ΔΣ ⊥ΔΣ] [es : (℘ Err) ∅])
                    ([k (in-list ks)])
            (⊕ (values Vs ΔΣ es)
               (if (or (integer? k) (arity-at-least? k)) (on-arity k) ???)))]
         [(and k (or (? index?) (? arity-at-least?))) (on-arity k)])]
      ;; Havoc and widen struct's public fields
      [(or (St 𝒾 _) (Guarded _ (St/C 𝒾 _ _) _))
       #:when 𝒾
       (⊕ (collapse Σ (app Σ (ℓ/tag 'st-ref (-𝒾-name 𝒾)) (get-public-accs 𝒾) (list {set V})))
          (collapse Σ (app Σ (ℓ/tag 'st-set! (-𝒾-name 𝒾)) (get-public-muts 𝒾) (list {set V} ●))))]
      ;; Havoc and widen vector's fields
      [(Guarded _ (or (? Vectof/C?) (? Vect/C?)) _)
       (define I (-● {set 'exact-nonnegative-integer?}))
       (⊕ (collapse Σ (app Σ (ℓ/tag 'vect-ref) {set 'vector-ref} (list {set V} {set I})))
          (collapse Σ (app Σ (ℓ/tag 'vect-set!) {set 'vector-set!} (list {set V} {set I} ●))))]
      [(Vect αs)
       (values (foldl (λ ([α : α] [Vs : V^]) (∪ Vs (unpack α Σ))) ∅ αs)
               (foldl (λ ([α : α] [ΔΣ : ΔΣ]) (⧺ ΔΣ (mut α ●))) ⊥ΔΣ αs)
               ∅)]
      [(Vect-Of αᵥ _)
       (values (unpack αᵥ Σ) (mut αᵥ ●) ∅)]
      ;; Hash
      [(or (? Hash-Of?) (Guarded _ (? Hash/C?) _))
       (collapse Σ (app Σ (ℓ/tag 'hash-ref) {set 'hash-ref} (list {set V} ●)))]
      ;; Set
      [(or (? Set-Of?) (Guarded _ (? Set/C?) _))
       (collapse Σ (app Σ (ℓ/tag 'set-ref) {set 'set-first} (list {set V})))]
      ;; TODO apply contract to unknown
      [(? C?) ???]
      [_ (values ∅ ⊥ΔΣ ∅)]))

  (: arity-of
     (case->
      [Clo → (U Natural arity-at-least)]
      [(U Clo Case-Clo Guarded) → (U Natural arity-at-least (Listof (U Natural arity-at-least)))]))
  (define arity-of
    (match-lambda
      [(Clo xs _ _ _) (shape xs)]
      [(Case-Clo clos _) (map arity-of clos)]
      [(Guarded _ (? Fn/C? C) α) (guard-arity-of C)]))

  (: guard-arity-of (case->
                     [==>i → (U Natural arity-at-least)]
                     [Fn/C → (U Natural arity-at-least (Listof (U Natural arity-at-least)))]))
  (define guard-arity-of
    (match-lambda
      [(==>i doms _) (shape doms)]
      [(Case-=> cases) (map guard-arity-of cases)]
      [(∀/C _ E _) (E-arity-of E)]))

  (: E-arity-of : E → (U Natural arity-at-least))
  (define E-arity-of
    (match-lambda
      [(-->i doms _) (shape doms)]
      [_ ???])) 

  (: ℓ/tag : (U Symbol Integer) * → ℓ)
  (define (ℓ/tag . tags) (loc->ℓ (loc 'havoc 0 0 tags)))

  (define-simple-macro (collapse Σ e)
    (let-values ([(r es) e])
      (match (collapse-R r)
        [(cons Ws ΔΣ) (values (collect-behavioral-values Ws (⧺ Σ ΔΣ)) ΔΣ es)]
        [#f (values ∅ ⊥ΔΣ es)])))
  (define-simple-macro (⊕ e₁ e₂)
    (let-values ([(Vs₁ ΔΣ₁ es₁) e₁]
                 [(Vs₂ ΔΣ₂ es₂) e₂])
      (values (∪ Vs₁ Vs₂) (ΔΣ⊔ ΔΣ₁ ΔΣ₂) (∪ es₁ es₂))))
  )
