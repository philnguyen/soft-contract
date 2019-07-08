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
         "../utils/vector.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit hv@
  (import static-info^ meta-functions^ ast-pretty-print^
          sto^ cache^ val^
          exec^ app^ gc^)
  (export hv^)

  (define ℓₕᵥ (loc->ℓ (loc 'havoc 0 0 '())))
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
        (match spec
          [(-p/c-item (-𝒾 x _) _ _)
           (-x (-𝒾 x path) (loc->ℓ (loc 'top-level-havoc 0 0 (list x))))]
          [(-p/c-item (? -o? o) _ _)
           (define x #|HACK|# (assert (show-e o) symbol?))
           (-x (-𝒾 x path) (loc->ℓ (loc 'top-level-havoc 0 0 (list x))))])))
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
            (collapse Σ αₕᵥ (app Σ ℓₕᵥ {set V} (make-list k ●)))]
           [(arity-at-least n)
            (define Vᵣ {set (-● {set 'list?})})
            (define W₀ (make-list n ●))
            (collapse Σ αₕᵥ (app/rest Σ ℓₕᵥ {set V} W₀ Vᵣ))]))
       (match (arity-of V)
         [(? list? ks)
          (define-values (ΔΣ* es*)
            (for/fold ([ΔΣ : (Option ΔΣ) #f] [es : (℘ Err) ∅])
                      ([k (in-list ks)])
              (⊕ (values ΔΣ es)
                 (if (or (integer? k) (arity-at-least? k)) (on-arity k) ???))))
          (values (assert ΔΣ*) es*)]
         [(and k (or (? index?) (? arity-at-least?))) (on-arity k)])]
      ;; Havoc and widen struct's public fields
      [(or (St (α:dyn (β:st-elems _ 𝒾) _) _) (Guarded _ (? St/C? (app St/C-tag 𝒾)) _))
       #:when 𝒾
       (⊕ (collapse Σ αₕᵥ (app Σ ℓₕᵥ (get-public-accs 𝒾) (list {set V})))
          (collapse Σ αₕᵥ (app Σ ℓₕᵥ (get-public-muts 𝒾) (list {set V} ●))))]
      ;; Havoc and widen vector's fields
      [(Guarded _ (or (? Vectof/C?) (? Vect/C?)) _)
       (define I (-● {set 'exact-nonnegative-integer?}))
       (⊕ (collapse Σ αₕᵥ (app Σ ℓₕᵥ {set 'vector-ref} (list {set V} {set I})))
          (collapse Σ αₕᵥ (app Σ ℓₕᵥ {set 'vector-set!} (list {set V} {set I} ●))))]
      [(Vect α)
       (values (⧺ (for/fold ([ΔΣ : ΔΣ ⊥ΔΣ]) ([Vs (in-vector (Σ@/blob α Σ))])
                    (⧺ ΔΣ (track-leaks Σ αₕᵥ Vs)))
                  (match-let ([(α:dyn (β:vect-elems _ n) _) α])
                    (mut α (make-vector n ●) Σ)))
               ∅)]
      [(Vect-Of αᵥ _)
       (values (⧺ (mut αᵥ ● Σ) (track-leaks Σ αₕᵥ (unpack αᵥ Σ))) ∅)]
      ;; Hash
      [(or (? Hash-Of?) (Guarded _ (? Hash/C?) _))
       (collapse Σ αₕᵥ (app Σ ℓₕᵥ {set 'hash-ref} (list {set V} ●)))]
      ;; Set
      [(or (? Set-Of?) (Guarded _ (? Set/C?) _))
       (collapse Σ αₕᵥ (app Σ ℓₕᵥ {set 'set-first} (list {set V})))]
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
      [(∀/C _ E _ _) (E-arity-of E)]))

  (: E-arity-of : (case->
                   [-->i → (U Natural arity-at-least)]
                   [E → (U Natural arity-at-least (Listof (U Natural arity-at-least)))]))
  (define E-arity-of
    (match-lambda
      [(-->i doms _) (shape doms)]
      [(case--> cases) (map E-arity-of cases)]
      [(-∀/c _ E _) (E-arity-of E)]
      [_ ???]))

  (define-simple-macro (collapse Σ αₕᵥ e)
    (let-values ([(r es) e])
      (match (collapse-R r)
        [(cons Ws ΔΣ)
         (values (⧺ ΔΣ (track-leaks (⧺ Σ ΔΣ) αₕᵥ (apply ∪ ∅ (set-map Ws W->V^)))) es)]
        [#f (values ⊥ΔΣ es)])))
  (define-simple-macro (⊕ e₁ e₂)
    (let-values ([(ΔΣ₁ es₁) e₁]
                 [(ΔΣ₂ es₂) e₂])
      (values (if ΔΣ₁ (ΔΣ⊔ ΔΣ₁ ΔΣ₂) ΔΣ₂) (∪ es₁ es₂))))

  (: behavioral? : V Σ → Boolean)
  ;; Check if value maybe behavioral.
  ;; `#t` is a conservative answer "maybe yes"
  ;; `#f` is a strong answer "definitely no"
  (define (behavioral? V₀ Σ)
    (define-set seen : α #:mutable? #t)

    (: check-α : α → Boolean)
    (define (check-α α)
      (cond [(seen-has? α) #f]
            [else (seen-add! α)
                  (define S (Σ@/raw α Σ))
                  (if (vector? S) (vector-ormap check-V^ S) (check-V^ S))]))

    (: check-V^ : V^ → Boolean)
    (define (check-V^ V^) (set-ormap check V^))

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
        [(St α _) (check-α α)]
        [(Vect α) (vector-ormap check-V^ (Σ@/blob α Σ))]
        [(Vect-Of α _) (check-α α)]
        [(Hash-Of αₖ αᵥ) (or (check-α αₖ) (check-α αᵥ))]
        [(Set-Of α) (check-α α)]
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
    (define-set seen : α)

    (: go-V^ : V^ ΔΣ → ΔΣ)
    (define (go-V^ V^ acc) (set-fold go-V acc V^))

    (: go-V : V ΔΣ → ΔΣ)
    (define (go-V V acc)
      (match V
        [(St (and α (α:dyn (β:st-elems _ (and 𝒾 (not (? prim-struct?)))) _)) _)
         #:when (not (seen-has? α))
         (seen-add! α)
         ;; Bucket values by fields, breaking correlation between fields
         (for/fold ([acc : ΔΣ acc]) ([(Vᵢ i) (in-indexed (Σ@/blob α Σ))])
           (go-V^ Vᵢ (⧺ acc (alloc (γ:escaped-field 𝒾 (assert i index?)) Vᵢ))))]
        [(Guarded ctx (St/C (? St/C? (app St/C-tag (and 𝒾 (not (? prim-struct?)))))) αᵥ) ; FIXME
         acc]
        [(-● Ps)
         (or (for/or : (Option ΔΣ) ([Pᵢ (in-set Ps)] #:when (-st-p? Pᵢ))
               (match-define (-st-p 𝒾) Pᵢ)
               (define m
                 (for/fold ([m : (HashTable Index (℘ P)) (hash)]) ([Pᵢ (in-set Ps)])
                   (match Pᵢ
                     [(P:St (cons (-st-ac (== 𝒾) i) acs) Q)
                      (define P* (if (null? acs) Q (P:St acs Q)))
                      (hash-update m i (λ ([Ps : (℘ P)]) (set-add Ps P*)) mk-∅)]
                     [_ m])))
               (for/fold ([acc : ΔΣ acc]) ([(i Ps) (in-hash m)])
                 (⧺ acc (alloc (γ:escaped-field 𝒾 i) {set (-● Ps)}))))
             acc)]
        [_ acc]))
    
    (go-V^ Vs ⊥ΔΣ))

  (: W->V^ : W → V^)
  (define (W->V^ W) ((inst foldl V^ V^) ∪ ∅ W))
  )
