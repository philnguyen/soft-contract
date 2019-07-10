#lang typed/racket/base

(provide gc@)

(require racket/set
         racket/match
         racket/splicing
         racket/vector
         (only-in racket/list partition)
         typed/racket/unit
         set-extras
         unreachable
         "../utils/vector.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(define-unit gc@
  (import meta-functions^ static-info^
          exec^
          sto^ val^)
  (export gc^)

  (: gc ([(℘ (U α T)) Σ] [Σ] . ->* . Σ))
  ;; Garbage collect store(-delta) `Σ₀` with respect to live addresses `root`.
  ;; The context `Σ-ctx` is the full store, which may or may not coincide with `Σ₀`
  (define (gc root Σ₀ [ctx Σ₀])
    (define-set touched : (U α T))
    (match-define (cons Ξ₀ Γ₀) Σ₀)

    (: touch : (U α T) Ξ Γ → (Values Ξ Γ))
    (define (touch α Ξ Γ)
      (touched-add! α)

      ;; Look up full context to span addresses,
      ;; but only copy entries from the store-delta in focus
      (define Ξ* (cond [(and (α? α) (hash-ref Ξ₀ α #f)) => (λ (r) (hash-set Ξ α r))]
                       [else Ξ]))
      (define Γ* (cond [(and (T? α) (hash-ref Γ₀ α #f)) => (λ (D) (hash-set Γ α D))]
                       [else Γ]))
      (define S
        (match α
          [(? α?) (Σ@/raw α ctx)] ;`Σ@` instead of just `hash-ref` takes care of `γ:imm`
          [(T:@ (? -st-ac?) _) (list (T-root α))]
          [_ (hash-ref (cdr ctx) α)]))

      (cond
        [(vector? S)
         (for*/fold ([Ξ* : ΔΞ Ξ*] [Γ* : ΔΓ Γ*])
                    ([Vs (in-vector S)]
                     [V (in-set Vs)]
                     [α* (in-set (V-root V))] #:unless (touched-has? α*))
           (touch α* Ξ* Γ*))]
        [(hash? S)
         (for/fold ([Ξ* : ΔΞ Ξ*] [Γ* : ΔΓ Γ*])
                   ([D (in-hash-values S)])
           (cond [(set? D)
                  (for*/fold ([Ξ* : ΔΞ Ξ*] [Γ* : ΔΓ Γ*])
                             ([V (in-set D)]
                              [α* (in-set (V-root V))]
                              ;; FIXME: Attempt to only touch "store-addresses"
                              ;; But this may accidentally omit top-level addreses,
                              ;; which are currently store
                              #:unless (and (not (γ:top? α*)) (T? α*))
                              #:unless (touched-has? α*))
                    (touch α* Ξ* Γ*))]
                 [(and (α:dyn? D) (not (touched-has? D))) (touch D Ξ* Γ*)]
                 [else (values Ξ* Γ*)]))]
        [(set? S)
         (for*/fold ([Ξ* : ΔΞ Ξ*] [Γ* : ΔΓ Γ*])
                    ([V (in-set S)]
                     [α* (in-set (V-root V))] #:unless (touched-has? α*))
           (touch α* Ξ* Γ*))]
        [(list? S)
         (for/fold ([Ξ* : ΔΞ Ξ*] [Γ* : ΔΓ Γ*])
                   ([T (in-set (car S))])
           (touch T Ξ* Γ*))]
        [(-prim? S) (values Ξ* Γ*)]
        [(T:@? S)
         (for/fold ([Ξ* : ΔΞ Ξ*] [Γ* : ΔΓ Γ*]) ([T (in-set (T-root S))])
           (touch T Ξ* Γ*))]
        [else (touch S Ξ* Γ*)]))

    (: touch* : (℘ (U α T)) Ξ Γ → (Values Ξ Γ))
    (define (touch* αs Ξ Γ)
      (for/fold ([Ξ : ΔΞ Ξ] [Γ : ΔΓ Γ]) ([α (in-set αs)])
        (touch α Ξ Γ)))

    (let-values ([(Ξ₁ Γ₁) (touch* root ⊥Ξ ⊤Γ)])
      (define Ξ* (if (= (hash-count Ξ₀) (hash-count Ξ₁)) Ξ₀ Ξ₁))
      (define Γ* (if (= (hash-count Γ₀) (hash-count Γ₁)) Γ₀ (retain-props touched Γ₀ Γ₁)))
      (if (and (eq? Ξ* Ξ₀) (eq? Γ* Γ₀))
          ;; Try to re-use old instance
          Σ₀
          (cons Ξ* Γ*))))

  (: retain-props : (℘ (U α T)) Γ Γ → Γ)
  (define (retain-props live Γ₀ Γ₁)
    (for/fold ([acc : Γ Γ₁]) ([(T D) (in-hash Γ₀)]
                              #:unless (hash-has-key? Γ₁ T)
                              ;; FIXME rid of hack by fixing `Γ` representation
                              #:when (prop? T D)
                              #:when (all-live? live T))
      (hash-set acc T D)))

  (: gc-R : (℘ (U α T)) Σ R → R)
  (define (gc-R root Σ r)
    (for/hash : R ([(W ΔΣs) (in-hash r)])
      (define root* (∪ root (W-root W)))
      (values W
              (for/fold ([acc : (℘ ΔΣ) ∅]) ([ΔΣᵢ : ΔΣ (in-set ΔΣs)])
                (ΔΣ⊔₁ (gc root* ΔΣᵢ (⧺ Σ ΔΣᵢ)) acc)))))

  (define V-root : (V → (℘ (U α T)))
    (match-lambda
      [(St α _) {set α}]
      [(Vect α) {set α}]
      [(Vect-Of αₑ Vₙ) (set-add (set-filter α? Vₙ) αₑ)]
      [(Hash-Of αₖ αᵥ) {set αₖ αᵥ}]
      [(Set-Of α) {set α}]
      [(? -λ? V) (E-root V)]
      [(? Clo? V) (Clo-root V)]
      [(Case-Clo clos _) (apply ∪ ∅ (map Clo-root clos))]
      [(Guarded _ C α) (set-add (V-root C) α)]
      [(Sealed α) ∅] ; TODO confirm ok
      [(And/C α₁ α₂ _) {set α₁ α₂}]
      [(Or/C α₁ α₂ _) {set α₁ α₂}]
      [(Not/C α _) {set α}]
      [(X/C α) {set α}]
      [(Seal/C α _) {set α}]
      [(? St/C? C)
       (define-values (αₕ _ 𝒾) (St/C-fields C))
       (set-add (if (prim-struct? 𝒾)
                    ∅
                    ;; TODO: this may not work properly with sub-structs
                    (for/set: : (℘ α) ([i (in-range (count-struct-fields 𝒾))])
                      (γ:escaped-field 𝒾 (assert i index?))))
                αₕ)]
      [(Vectof/C α _) {set α}]
      [(Vect/C α) {set α}]
      [(Hash/C αₖ αᵥ _) {set αₖ αᵥ}]
      [(Set/C α _) {set α}]
      [(? ==>i? V) (==>i-root V)]
      [(∀/C xs c α) (E-H-root xs c α)]
      [(Case-=> Cs) (apply ∪ ∅ (map ==>i-root Cs))] 
      [(? -prim? p) (prim-root p)]
      [(or (? -prim?) (? One-Of/C?) (? -●?) (? Empty-Set?) (? Empty-Hash?) (? P?)) ∅]))

  (define Clo-root : (Clo → (℘ α))
    (match-lambda [(Clo fml E α) (E-H-root fml E α)]))

  (define E-H-root : ((U -formals (Listof Symbol)) E α → (℘ α))
    (let ([$ : (Mutable-HashTable E (℘ α)) (make-hasheq)])
      (λ (fml E α)
        (define tops (hash-ref!
                      $ E
                      (λ ()
                        (set-filter (λ (α) (not (γ:lex? α))) (E-root E)))))
        (set-add tops α))))

  (: D-root : D → (℘ (U α T)))
  (define (D-root D)
    (cond [(set? D) (set-union-map V-root D)]
          [(-prim? D) ∅]
          [(T:@? D) (T-root D)]
          [else {set D}]))

  (: W-root : W → (℘ (U α T)))
  (define (W-root W) (apply ∪ ∅ (map D-root W)))

  (define ==>i-root : (==>i → (℘ α))
    (match-lambda
      [(==>i (-var doms ?doms:rst) rng _)
       (∪ (apply ∪ (if ?doms:rst (Dom-root ?doms:rst) ∅) (map Dom-root doms))
          (if rng (apply ∪ ∅ (map Dom-root rng)) ∅))]))

  (define Dom-root : (Dom → (℘ α))
    (match-lambda [(Dom _ C _) (if (Clo? C) (Clo-root C) {set C})]))

  (splicing-local
      ((define E-root-cache : (Mutable-HashTable E (℘ γ)) (make-hasheq))
       (define prim-root-cache : (Mutable-HashTable -prim (℘ γ)) (make-hash)))

    (: E-root : E → (℘ γ))
    ;; Compute free variables for expression. Return set of variable names.
    (define (E-root E)
      (hash-ref!
       E-root-cache E
       (λ ()
         (match E
           [(? -prim? p) (prim-root p)]
           [(? -•?) {set (γ:hv #f)}]
           [(-x x ℓ)
            (cond [(symbol? x) {set (γ:lex x)}]
                  [(equal? (ℓ-src ℓ) (-𝒾-src x)) {set (γ:top x)}]
                  [else {set #|want both due to Racket's internal opt.|# (γ:top x) (γ:wrp x)}])]
           [(-λ xs e _) (set-subtract (E-root e) (map/set γ:lex (formals->names xs #:eq? #f)))]
           [(-case-λ cases _) (apply ∪ ∅ (map E-root cases))]
           [(-@ f xs _) (apply ∪ (E-root f) (map E-root xs))]
           [(-begin es) (apply ∪ ∅ (map E-root es))]
           [(-begin0 e₀ es) (apply ∪ (E-root e₀) (map E-root es))]
           [(-let-values bnds e _)
            (define-values (bound rhs:E-root)
              (for/fold ([bound : (℘ γ) ∅] [rhs:E-root : (℘ γ) ∅])
                        ([bnd bnds])
                (match-define (cons xs rhs) bnd)
                (values (set-add* bound (map γ:lex xs)) (∪ rhs:E-root (E-root rhs)))))
            (∪ rhs:E-root (set-subtract (E-root e) bound))]
           [(-letrec-values bnds e _)
            (define bound (for/fold ([bound : (℘ γ) ∅]) ([bnd bnds])
                            (set-add* bound (map γ:lex (car bnd)))))
            (set-subtract (apply ∪ (E-root e) (map (compose1 E-root (inst cdr Any -e)) bnds)) bound)]
           [(-set! x e _) (set-add (E-root e) (if (symbol? x) (γ:lex x) (γ:top x)))]
           [(-if e e₁ e₂ _) (∪ (E-root e) (E-root e₁) (E-root e₂))]
           [(-μ/c x e) (set-remove (E-root e) (γ:lex x))]
           [(-->i (-var cs c) d _)
            (define dom-E-root : (-dom → (℘ γ))
              (match-lambda
                [(-dom _ ?xs d _) (set-subtract (E-root d) (if ?xs (list->set (map γ:lex ?xs)) ∅))]))
            (∪ (apply ∪ (if c (dom-E-root c) ∅) (map dom-E-root cs))
               (if d (apply ∪ ∅ (map dom-E-root d)) ∅))]
           [(case--> cases) (apply ∪ ∅ (map E-root cases))]
           [E (log-debug "E-ROOT⟦~a⟧ = ∅~n" E) ∅]))))

    (: prim-root : -prim → (℘ γ))
    (define (prim-root p)
      (hash-ref!
       prim-root-cache p
       (λ ()
         (match p
           [(-st-ac 𝒾 i) (if (prim-struct? 𝒾) ∅ {set (γ:escaped-field 𝒾 i)})]
           ['unsafe-struct-ref
            (for*/set: : (℘ γ) ([𝒾 (in-struct-tags)]
                                #:unless (prim-struct? 𝒾)
                                [i (in-range (count-struct-fields 𝒾))])
              (γ:escaped-field 𝒾 (assert i index?)))]
           [(? symbol? o) {set (γ:hv o)}]
           [_ ∅]))))

    (: T-root : T:@ → (℘ T))
    ;; Compute terms mentioned by `T₀`
    (define (T-root T₀)
      (: go : (U T -prim) → (℘ T))
      (define (go T)
        (match T
          [(T:@ K Ts)
           (∪ (go-K K) (apply ∪ (if (-st-ac? K) ∅ {set T}) (map go Ts)))]
          [(? -prim?) ∅]
          [(? γ? γ) {set γ}]))
      (: go-K : K → (℘ T))
      (define go-K
        (match-lambda
          [(? -prim? p) (prim-root p)]
          [(? T? T) (go T)]
          [_ ∅]))
      (go T₀))

    (: all-live? : (℘ (U α T)) T → Boolean)
    (define (all-live? γs T₀)
      (define (go-T [x : (U T -prim)]) : Boolean
        (cond [(∋ γs x) #t]
              [(T:@? x) (and (go-K (T:@-_0 x)) (andmap go-T (T:@-_1 x)))]
              [else (not (γ:lex? x))]))
      (define (go-K [K : K]) (if (T? K) (∋ γs K) #t))
      (go-T T₀))

    ;; Cache for computing live variables depend on specific program's information
    ;; such as struct tags (for computing addresses to leaked fields kept live by
    ;; `unsafe-struct-ref`),
    ;; so can't be re-used across different programs
    (define (clear-live-set-cache!)
      (hash-clear! E-root-cache)
      (hash-clear! prim-root-cache)))
  )
