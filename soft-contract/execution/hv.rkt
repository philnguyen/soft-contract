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
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit hv@
  (import static-info^ meta-functions^
          sto^ cache^ val^
          exec^ app^ gc^)
  (export hv^)

  (define ● {set (-● ∅)})
  (define ●* (list ●)) ; FIXME emulate *arbitrary* number of values

  (: leak : Σ γ:hv V^ → (Values R (℘ Err)))
  (define (leak Σ αₕᵥ Vs)
    (define ΔΣ (track-leaks Σ αₕᵥ Vs))
    (with-pre ΔΣ (hv (⧺ Σ ΔΣ) αₕᵥ)))

  (: track-leaks : Σ γ:hv V^ → ΔΣ)
  (define (track-leaks Σ αₕᵥ Vs)
    (⧺ (alloc αₕᵥ (collect-behavioral-values Vs Σ))
       ;; only track field leaks for `havoc` for now
       (if (γ:hv-_0 αₕᵥ) ⊥ΔΣ (track-field-leaks Vs Σ))))

  (: hv : Σ γ:hv → (Values R (℘ Err)))
  (define (hv Σ αₕᵥ)
    (define root {set αₕᵥ})
    (define Σ* (gc root Σ))
    (ref-$! ($:Key:Hv Σ* αₕᵥ)
            (λ ()
              (with-gc root Σ*
                (λ ()
                  ;; Next "productive" havoc step on each leaked value
                  (define-values (ΔΣ₁ es₁)
                    (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ] [es : (℘ Err) ∅])
                              ([Vᵢ (in-set (unpack αₕᵥ Σ*))])
                      (⊕ (values ΔΣ es) (do-hv Σ* αₕᵥ Vᵢ))))
                  ;; Recursively havoc again
                  (with-collapsing [(ΔΣ* _) (hv (⧺ Σ* ΔΣ₁) αₕᵥ)]
                    #:fail (R-of ●* ΔΣ₁)
                    (values (R-of ●* (ΔΣ⊔ ΔΣ₁ (⧺ ΔΣ₁ ΔΣ*))) es₁)))))))

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

  (: do-hv : Σ γ:hv V → (Values ΔΣ (℘ Err)))
  ;; Havoc the value and collect behavioral values discovered
  (define (do-hv Σ αₕᵥ V)
    (match V
      ;; Apply function to appropriate number of args
      [(or (? Clo?) (? Case-Clo?) (Guarded _ (? Fn/C?) _))
       (define on-arity : ((U Natural arity-at-least) → (Values ΔΣ (℘ Err)))
         (match-lambda
           [(? index? k)
            (collapse Σ αₕᵥ (app Σ (ℓ/tag 'app k) {set V} (make-list k ●)))]
           [(arity-at-least n)
            (define Vᵣ {set (-● {set 'list?})})
            (define W₀ (make-list n ●))
            (collapse Σ αₕᵥ (app/rest Σ (ℓ/tag 'app 'varargs) {set V} W₀ Vᵣ))]))
       (match (arity-of V)
         [(? list? ks)
          (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ] [es : (℘ Err) ∅])
                    ([k (in-list ks)])
            (⊕ (values ΔΣ es)
               (if (or (integer? k) (arity-at-least? k)) (on-arity k) ???)))]
         [(and k (or (? index?) (? arity-at-least?))) (on-arity k)])]
      ;; Havoc and widen struct's public fields
      [(or (St 𝒾 _ _) (Guarded _ (St/C 𝒾 _ _) _))
       #:when 𝒾
       (⊕ (collapse Σ αₕᵥ (app Σ (ℓ/tag 'st-ref (-𝒾-name 𝒾)) (get-public-accs 𝒾) (list {set V})))
          (collapse Σ αₕᵥ (app Σ (ℓ/tag 'st-set! (-𝒾-name 𝒾)) (get-public-muts 𝒾) (list {set V} ●))))]
      ;; Havoc and widen vector's fields
      [(Guarded _ (or (? Vectof/C?) (? Vect/C?)) _)
       (define I (-● {set 'exact-nonnegative-integer?}))
       (⊕ (collapse Σ αₕᵥ (app Σ (ℓ/tag 'vect-ref) {set 'vector-ref} (list {set V} {set I})))
          (collapse Σ αₕᵥ (app Σ (ℓ/tag 'vect-set!) {set 'vector-set!} (list {set V} {set I} ●))))]
      [(Vect αs)
       (values (foldl (λ ([α : α] [ΔΣ : ΔΣ])
                        (⧺ ΔΣ (mut α ●) (track-leaks Σ αₕᵥ (unpack α Σ))))
                      ⊥ΔΣ αs)
               ∅)]
      [(Vect-Of αᵥ _)
       (values (⧺ (mut αᵥ ●) (track-leaks Σ αₕᵥ (unpack αᵥ Σ))) ∅)]
      ;; Hash
      [(or (? Hash-Of?) (Guarded _ (? Hash/C?) _))
       (collapse Σ αₕᵥ (app Σ (ℓ/tag 'hash-ref) {set 'hash-ref} (list {set V} ●)))]
      ;; Set
      [(or (? Set-Of?) (Guarded _ (? Set/C?) _))
       (collapse Σ αₕᵥ (app Σ (ℓ/tag 'set-ref) {set 'set-first} (list {set V})))]
      ;; TODO apply contract to unknown
      [(? C?) (values ⊥ΔΣ ∅)]
      [_ (values ⊥ΔΣ ∅)]))

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

  (: E-arity-of : (case->
                   [-->i → (U Natural arity-at-least)]
                   [E → (U Natural arity-at-least (Listof (U Natural arity-at-least)))]))
  (define E-arity-of
    (match-lambda
      [(-->i doms _) (shape doms)]
      [(case--> cases) (map E-arity-of cases)]
      [(-∀/c _ E) (E-arity-of E)]
      [_ ???]))

  (: ℓ/tag : (U Symbol Integer) * → ℓ)
  (define (ℓ/tag . tags) (loc->ℓ (loc 'havoc 0 0 tags)))

  (define-simple-macro (collapse Σ αₕᵥ e)
    (let-values ([(r es) e])
      (match (collapse-R r)
        [(cons Ws ΔΣ)
         (values (⧺ ΔΣ (track-leaks (⧺ Σ ΔΣ) αₕᵥ (apply ∪ ∅ (set-map Ws W->V^)))) es)]
        [#f (values ⊥ΔΣ es)])))
  (define-simple-macro (⊕ e₁ e₂)
    (let-values ([(ΔΣ₁ es₁) e₁]
                 [(ΔΣ₂ es₂) e₂])
      (values (ΔΣ⊔ ΔΣ₁ ΔΣ₂) (∪ es₁ es₂))))

  (: behavioral? : V Σ → Boolean)
  ;; Check if value maybe behavioral.
  ;; `#t` is a conservative answer "maybe yes"
  ;; `#f` is a strong answer "definitely no"
  (define (behavioral? V₀ Σ)
    (define-set seen : α #:as-mutable-hash? #t)

    (: check-α : α → Boolean)
    (define (check-α α)
      (cond [(seen-has? α) #f]
            [else (seen-add! α)
                  (set-ormap check (Σ@ α Σ))]))

    (define check-==>i : (==>i → Boolean)
      (match-lambda
        [(==>i (-var init rest) rng)
         (or (ormap check-dom init)
             (and rest (check-dom rest))
             (and rng (ormap check-dom rng)))]))

    (define check-dom : (Dom → Boolean)
      (match-lambda
        [(Dom _ C _) (if (Clo? C) #t (check-α C))]))

    (define check : (V → Boolean)
      (match-lambda
        [(St _ αs _) (ormap check-α αs)]
        [(Vect αs) (ormap check-α αs)]
        [(Vect-Of α _) (check-α α)]
        [(Hash-Of αₖ αᵥ im?) (or (not im?) (check-α αₖ) (check-α αᵥ))]
        [(Set-Of α im?) (or (not im?) (check-α α))]
        [(Guarded _ G α) (or (Fn/C? G) (check-α α))]
        [(? ==>i? V) (check-==>i V)]
        [(Case-=> cases) (ormap check-==>i cases)]
        [(or (? Clo?) (? Case-Clo?)) #t]
        [(? T? T) (set-ormap check (unpack T Σ))]
        [_ #f]))

    (check V₀))

  (: collect-behavioral-values : (℘ (U V W)) Σ → V^)
  (define (collect-behavioral-values xs Σ)
    (: go-V : V V^ → V^)
    (define (go-V V acc) (if (behavioral? V Σ) (set-add acc V) acc))
    (: go-W : W V^ → V^)
    (define (go-W W acc)
      (for*/fold ([acc : V^ acc]) ([Vs (in-list W)] [V (in-set Vs)])
        (go-V V acc)))
    (for/fold ([acc : V^ ∅]) ([x (in-set xs)])
      (if (list? x) (go-W x acc) (go-V x acc))))

  (: track-field-leaks : V^ Σ → ΔΣ)
  (define (track-field-leaks Vs Σ)
    (define seen : (HashTable α #t) (make-hash))

    (: go-α : α -𝒾 Index ΔΣ → ΔΣ)
    (define (go-α α 𝒾 i acc)
      (if (hash-has-key? seen α)
          acc
          (let ()
            (hash-set! seen α #t)
            (define Vs (Σ@ α Σ))
            (go-V^ Vs (⧺ acc (alloc (γ:escaped-field 𝒾 i) Vs))))))

    (: go-V^ : V^ ΔΣ → ΔΣ)
    (define (go-V^ V^ acc) (set-fold go-V acc V^))

    (: go-V : V ΔΣ → ΔΣ)
    (define (go-V V acc)
      (match V
        [(St (and 𝒾 (not (? prim-struct?))) αs _)
         ;; Bucket values by fields, breaking correlation between fields
         (for/fold ([acc : ΔΣ acc]) ([αᵢ (in-list αs)] [i (in-naturals)])
           (go-α αᵢ 𝒾 (assert i index?) acc))]
        [(Guarded ctx (St/C (and 𝒾 (not (? prim-struct?))) αs _) αᵥ) ; FIXME
         acc]
        [_ acc]))
    
    (go-V^ Vs ⊥ΔΣ))

  (: W->V^ : W → V^)
  (define (W->V^ W) ((inst foldl V^ V^) ∪ ∅ W))
  )
