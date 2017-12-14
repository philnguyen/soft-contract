#lang typed/racket/base

(provide app@)

(require racket/set
         racket/match
         racket/list
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
          mon^ compile^ kont^ proof-system^ prims^ memoize^ havoc^
          env^ val^ path^ instr^ sto^ pretty-print^ for-gc^)
  (export app^)

  (: app : ℓ -V^ (Listof -V^) -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (app ℓ Vₕ^ Vₓ^s H φ Σ ⟦k⟧)
    (for/union : (℘ -ς) ([Vₕ (in-set Vₕ^)])
      (define-values (H* looped?)
        (if (or (-Clo? Vₕ) (-Ar? Vₕ))
            (H+ H (-edge (strip-fn Vₕ) ℓ))
            (values H #f)))
      (define ⟦k⟧* (restore-ctx∷ H ⟦k⟧))
      (define αₖ
        (let ([αₖ (-αₖ H* (-B Vₕ Vₓ^s ℓ) φ)])
          (if (-o? Vₕ) αₖ (σₖ+! Σ αₖ ⟦k⟧*))))
      (if looped?
          {set (-ς↑ αₖ)}
          (app₁ ℓ Vₕ Vₓ^s H* φ Σ ⟦k⟧*))))

  (: app₁ ([ℓ -V (Listof -V^) -H -φ -Σ -⟦k⟧] [#:switched? Boolean] . ->* . (℘ -ς)))
  (define (app₁ ℓ Vₕ Vₓs H φ Σ ⟦k⟧ #:switched? [switched? #f])
    (define l (ℓ-src ℓ))
    (define σ (-Σ-σ Σ))

    (: blm-arity : Arity Natural → -blm)
    (define (blm-arity required provided)
      ;; HACK for error message. Probably no need to fix
      (define msg (string->symbol (format "require ~a arguments" required)))
      (blm/simp l 'Λ (list msg) Vₓs ℓ))

    (define-syntax-rule (with-guarded-arity a* e ...)
      (let ([n (length Vₓs)]
            [a a*])
        (cond
          [(arity-includes? a n) e ...]
          [else (⟦k⟧ (blm-arity a n) H φ Σ)])))

    (define (app-And/C [V₁ : -V^] [V₂ : -V^])
      (define ⟦rhs⟧ (mk-app ℓ (mk-A (list V₂)) (list (mk-A Vₓs))))
      (app ℓ V₁ Vₓs H φ Σ (and∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))

    (define (app-Or/C [V₁ : -V^] [V₂ : -V^])
      (define ⟦rhs⟧ (mk-app ℓ (mk-A (list V₂)) (list (mk-A Vₓs))))
      (app ℓ V₁ Vₓs H φ Σ (or∷ l (list ⟦rhs⟧) ⊥ρ ⟦k⟧)))
    
    (define (app-Not/C [Vᵤ : -V^])
      (app ℓ Vᵤ Vₓs H φ Σ (ap∷ (list {set 'not}) '() ⊥ρ ℓ ⟦k⟧)))

    (define (app-One-Of/C [bs : (℘ Base)])
      (define Vₐ
        (case (sat-one-of (car Vₓs) bs)
          [(✓) -tt]
          [(✗) -ff]
          [(?) (-● {set 'boolean?})]))
      (⟦k⟧ (list {set Vₐ}) H φ Σ))

    (define (app-St/C [𝒾 : -𝒾] [Cs : (Listof -V^)])
      ;; TODO fix ℓ
      (match Vₓs
        [(list (or (-St 𝒾* _) (-St* (-St/C _ 𝒾* _) _ _)))
         #:when (𝒾* . substruct? . 𝒾)
         (define ⟦chk-field⟧s : (Listof -⟦e⟧)
           (for/list ([Cᵢ^ (in-list Cs)] [i (in-naturals)] #:when (index? i))
             (define ac (-st-ac 𝒾 i))
             (mk-app ℓ (mk-A (list Cᵢ^)) (list (mk-app ℓ (mk-V ac) (list (mk-A Vₓs)))))))
         (app₁ ℓ (-st-p 𝒾) Vₓs H φ Σ (and∷ l ⟦chk-field⟧s ⊥ρ ⟦k⟧))]
        [_
         (⟦k⟧ (list {set -ff}) H φ Σ)]))

    (match Vₕ
      ;; In the presence of struct contracts, field accessing is not an atomic operation
      ;; because structs can be contract-wrapped arbitrarily deeply,
      ;; plus contracts can be arbitrary code.
      ;; This means field accessing cannot be implemented in `δ`
      [(-st-p  𝒾) ((app-st-p 𝒾) ℓ Vₓs H φ Σ ⟦k⟧)]
      [(-st-mk 𝒾) ((app-st-mk 𝒾) ℓ Vₓs H φ Σ ⟦k⟧)]
      [(-st-ac  𝒾 i) ((app-st-ac  𝒾 i) ℓ Vₓs H φ Σ ⟦k⟧)]
      [(-st-mut 𝒾 i) ((app-st-mut 𝒾 i) ℓ Vₓs H φ Σ ⟦k⟧)]
      ['make-sequence (app-make-sequence ℓ Vₓs H φ Σ ⟦k⟧)]

      ;; Regular stuff
      [(? symbol? o) ((get-prim o) ℓ Vₓs H φ Σ ⟦k⟧)]
      [(-Clo xs ⟦e⟧ ρ)
       (with-guarded-arity (shape xs)
         ((app-clo xs ⟦e⟧ ρ #:switched? switched?) ℓ Vₓs H φ Σ ⟦k⟧))]
      [(? -Case-Clo?)
       ((app-Case-Clo Vₕ) ℓ Vₓs H φ Σ ⟦k⟧)]
      [(-Ar C α ctx)
       (with-guarded-arity (guard-arity C)
         (define Vᵤ^ (set-remove (σ@ Σ (-φ-cache φ) α) Vₕ))
         (define f (cond [(-=>? C) (app-Ar C Vᵤ^ ctx)]
                         [(-=>i? C) (app-Indy C Vᵤ^ ctx)]
                         [(-∀/C? C) (app-∀/C C Vᵤ^ ctx)]
                         [else (app-guarded-Case C Vᵤ^ ctx)]))
         (f ℓ Vₓs H φ Σ ⟦k⟧))]
      [(-And/C #t (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (with-guarded-arity 1
         (app-And/C (σ@ Σ (-φ-cache φ) α₁) (σ@ Σ (-φ-cache φ) α₂)))]
      [(-Or/C #t (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (with-guarded-arity 1
         (app-Or/C (σ@ Σ (-φ-cache φ) α₁) (σ@ Σ (-φ-cache φ) α₂)))]
      [(-Not/C (-⟪α⟫ℓ α ℓ*))
       (with-guarded-arity 1
         (app-Not/C (σ@ Σ (-φ-cache φ) α)))]
      [(-One-Of/C vals)
       (with-guarded-arity 1
         (app-One-Of/C vals))]
      [(-St/C #t s αℓs)
       (with-guarded-arity 1
         (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
         (app-St/C s (σ@/list σ (-φ-cache φ) αs)))]
      [(->/c (? real? r))
       (app₁ ℓ '>  (list (car Vₓs) {set (-b r)}) H φ Σ ⟦k⟧)]
      [(-≥/c (? real? r))
       (app₁ ℓ '>= (list (car Vₓs) {set (-b r)}) H φ Σ ⟦k⟧)]
      [(-</c (? real? r))
       (app₁ ℓ '<  (list (car Vₓs) {set (-b r)}) H φ Σ ⟦k⟧)]
      [(-≤/c (? real? r))
       (app₁ ℓ '<= (list (car Vₓs) {set (-b r)}) H φ Σ ⟦k⟧)]
      [(or (? integer?) (? -●?) (? -Fn●?))
       (define l (ℓ-src ℓ))

       (: blm : -h -φ → (℘ -ς))
       (define (blm C φ)
         (define blm (blm/simp l 'Λ (list C) (list {set Vₕ}) ℓ))
         (⟦k⟧ blm H φ Σ))

       (: chk-arity : -φ → (℘ -ς))
       (define (chk-arity φ)
         (define num-args (length Vₓs))
         (define Vₕ-arity (cond [(V-arity Vₕ) => -b]
                                [(-t? Vₕ) (-t.@ 'procedure-arity (list Vₕ))]
                                [else (-● ∅)]))
         (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ 'arity-includes? {set Vₕ-arity} {set (-b num-args)})])
           : -ς
           #:true  ((app-opq Vₕ) ℓ Vₓs H φ₁ Σ ⟦k⟧)
           #:false (blm (format-symbol "(arity-includes/c ~a)" num-args) φ₂)))

       (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ σ φ 'procedure? {set Vₕ})]) : -ς
         #:true  (chk-arity φ₁)
         #:false (blm 'procedure? φ₂))]
      [_
       (define blm (blm/simp l 'Λ (list 'procedure?) (list {set Vₕ}) ℓ))
       (⟦k⟧ blm H φ Σ)]))

  (: app-clo ([-formals -⟦e⟧ -ρ] [#:switched? Boolean] . ->* . -⟦f⟧))
  (define ((app-clo xs ⟦e⟧ ρ #:switched? [switched? #f]) ℓ Vₓs H φ Σ ⟦k⟧)
    (define-values (ρ* φ*) (bind-args Σ ρ ℓ H φ xs Vₓs))
    (define ⟦k⟧*
      (if switched?
          (let* ([overlap
                  (for/seteq: : (℘ ⟪α⟫) ([α (in-hash-values ρ*)]
                                         #:when (hash-has-key? (-φ-cache φ) α))
                    α)]
                 [δσ
                  (for*/hasheq : -δσ ([α : ⟪α⟫ (in-set overlap)])
                    (values α (hash-ref (-φ-cache φ) α)))]
                 [deps
                  (for/fold ([deps : -δσ (span-δσ Σ (-φ-cache φ) overlap)])
                            ([α (in-set overlap)])
                    (hash-remove deps α))])
            (maybe-unshadow∷ δσ deps ⟦k⟧))
          ⟦k⟧))
    (⟦e⟧ ρ* H φ* Σ ⟦k⟧*))

  (: app-Case-Clo : -Case-Clo → -⟦f⟧)
  (define ((app-Case-Clo cases) ℓ Vₓs H φ Σ ⟦k⟧)
    (define n (length Vₓs))
    (define ?case
      (for/or : (Option -Clo) ([clo : -Clo (-Case-Clo-cases cases)]
                               #:when (arity-includes? (assert (V-arity clo)) n))
        clo))
    (match ?case
      [(-Clo xs ⟦e⟧ ρ)
       ((app-clo xs ⟦e⟧ ρ) ℓ Vₓs H φ Σ ⟦k⟧)]
      [#f
       (define msg (string->symbol (format "arity ~v" (V-arity cases))))
       (define blm (blm/simp (ℓ-src ℓ) 'Λ (list msg) Vₓs ℓ))
       (⟦k⟧ blm H φ Σ)]))

  (: app-Ar : -=> -V^ -ctx → -⟦f⟧)
  (define ((app-Ar C Vᵤ^ ctx) ℓₐ Vₓs H φ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (define ctx* (ctx-neg ctx))
    (match-define (-=> αℓs Rng) C)
    (define ⟦k⟧/mon-rng (mon*.c∷ (ctx-with-ℓ ctx ℓₐ) Rng ⟦k⟧))
    (define ℓₐ* (ℓ-with-src ℓₐ (-ctx-src ctx)))
    (match αℓs
      ['()
       (app ℓₐ* Vᵤ^ '() H φ Σ ⟦k⟧/mon-rng)]
      [(? pair?)
       (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
       (define Cs (σ@/list σ (-φ-cache φ) αs))
       (match-define (cons ⟦mon-x⟧ ⟦mon-x⟧s)
         (for/list : (Listof -⟦e⟧) ([C^ Cs] [Vₓ^ Vₓs] [ℓₓ : ℓ ℓs])
           (mk-mon (ctx-with-ℓ ctx* ℓₓ) (mk-A (list C^)) (mk-A (list Vₓ^)))))
       (⟦mon-x⟧ ⊥ρ H φ Σ (ap∷ (list Vᵤ^) ⟦mon-x⟧s ⊥ρ ℓₐ* ⟦k⟧/mon-rng))]
      [(-var αℓs₀ αℓᵣ)
       (define-values (αs₀ ℓs₀) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs₀))
       (match-define (-⟪α⟫ℓ αᵣ ℓᵣ) αℓᵣ)
       (define-values (Vᵢs Vᵣs) (split-at Vₓs (length αs₀)))
       (define-values (Vᵣ φ*) (alloc-rest-args Σ ℓₐ H φ Vᵣs))
       (define ⟦mon-x⟧s : (Listof -⟦e⟧)
         (for/list ([Cₓ (σ@/list σ (-φ-cache φ*) αs₀)] [Vₓ Vᵢs] [ℓₓ : ℓ ℓs₀])
           (mk-mon (ctx-with-ℓ ctx* ℓₓ) (mk-A (list Cₓ)) (mk-A (list Vₓ)))))
       (define ⟦mon-x⟧ᵣ : -⟦e⟧
         (mk-mon (ctx-with-ℓ ctx* ℓᵣ) (mk-A (list (σ@ σ (-φ-cache φ*) αᵣ))) (mk-V Vᵣ)))
       (define fn (list Vᵤ^ {set 'apply}))
       (match ⟦mon-x⟧s
         ['()
          (define ⟦k⟧* (ap∷ fn '() ⊥ρ ℓₐ* ⟦k⟧/mon-rng))
          (⟦mon-x⟧ᵣ ⊥ρ H φ Σ ⟦k⟧*)]
         [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
          (define ⟦k⟧* (ap∷ fn `(,@⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ ℓₐ* ⟦k⟧/mon-rng))
          (⟦mon-x⟧₀ ⊥ρ H φ Σ ⟦k⟧*)])]))

  (: app-guarded-Case : -Case-> -V^ -ctx → -⟦f⟧)
  (define ((app-guarded-Case C Vᵤ^ ctx) ℓ Vₓs H φ Σ ⟦k⟧)
    (define n (length Vₓs))
    (define ?Cᵢ
      (for/or : (Option -=>) ([Cᵢ (in-list (-Case->-_0 C))]
                              #:when (arity-includes? (guard-arity Cᵢ) n))
        Cᵢ))
    (cond
      [?Cᵢ ((app-Ar ?Cᵢ Vᵤ^ ctx) ℓ Vₓs H φ Σ ⟦k⟧)]
      [else
       (define msg (string->symbol (format "arity ~v" (guard-arity C))))
       (define blm (blm/simp (ℓ-src ℓ) 'Λ (list msg) Vₓs ℓ))
       (⟦k⟧ blm H φ Σ)])) 

  (: app-∀/C : -∀/C -V^ -ctx → -⟦f⟧)
  (define ((app-∀/C C Vᵤ^ ctx) ℓₐ Vₓs H φ Σ ⟦k⟧)
    (define l-seal (-ctx-neg ctx))
    (match-define (-∀/C xs ⟦c⟧ ρ) C)
    (define-values (ρ* φ*)
      (for/fold ([ρ : -ρ ρ] [φ : -φ φ]) ([x (in-list xs)])
        (define αₛ (-α->⟪α⟫ (-α.imm (-Seal/C x H l-seal))))
        (define αᵥ (-α->⟪α⟫ (-α.sealed x H)))
        (values (ρ+ ρ x αₛ) (alloc Σ φ αᵥ ∅))))
    (define ⟦arg⟧s : (Listof -⟦e⟧) (for/list ([Vₓ (in-list Vₓs)]) (mk-A (list Vₓ))))
    (define ⟦k⟧* (mon.v∷ ctx Vᵤ^ (ap∷ '() ⟦arg⟧s ⊥ρ ℓₐ ⟦k⟧)))
    (⟦c⟧ ρ* H φ* Σ ⟦k⟧*))

  (: apply-app-Ar : (-=> -V^ -ctx → ℓ (Listof -V^) -V -H -φ -Σ -⟦k⟧ → (℘ -ς)))
  (define ((apply-app-Ar C Vᵤ^ ctx) ℓ₀ Vᵢs Vᵣ H φ Σ ⟦k⟧)
    (match-define (-=> (-var αℓs₀ (-⟪α⟫ℓ αᵣ ℓᵣ)) Rng) C)
    ;; FIXME copied n pasted from app-Ar
    (define-values (αs₀ ℓs₀) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs₀))
    (define ctx* (ctx-neg ctx))
    (define Cᵢs (σ@/list Σ (-φ-cache φ) αs₀))
    (define Cᵣ (σ@ Σ (-φ-cache φ) αᵣ))
    (define ⟦mon-x⟧s : (Listof -⟦e⟧)
      (for/list ([Cₓ Cᵢs] [Vₓ Vᵢs] [ℓₓ : ℓ ℓs₀])
        (mk-mon (ctx-with-ℓ ctx* ℓₓ) (mk-A (list Cₓ)) (mk-A (list Vₓ)))))
    (define ⟦mon-x⟧ᵣ : -⟦e⟧
      (mk-mon (ctx-with-ℓ ctx* ℓᵣ) (mk-A (list Cᵣ)) (mk-V Vᵣ)))
    (define fn (list Vᵤ^ {set 'apply}))
    (define ⟦k⟧* (mon*.c∷ (ctx-with-ℓ ctx ℓ₀) Rng ⟦k⟧))
    (match ⟦mon-x⟧s
      ['()
       (⟦mon-x⟧ᵣ ⊥ρ H φ Σ (ap∷ fn '() ⊥ρ ℓ₀ ⟦k⟧*))]
      [(cons ⟦mon-x⟧₀ ⟦mon-x⟧s*)
       (⟦mon-x⟧₀ ⊥ρ H φ Σ (ap∷ fn `(,@ ⟦mon-x⟧s* ,⟦mon-x⟧ᵣ) ⊥ρ ℓ₀ ⟦k⟧*))]))

  (: app-Indy : -=>i -V^ -ctx → -⟦f⟧)
  (define ((app-Indy C Vᵤ^ ctx) ℓₐ Vₓs H φ Σ ⟦k⟧)
    (define lo (-ctx-src ctx))
    (match-define (-=>i αℓs (cons Mk-D ℓᵣ)) C)
    (match-define (-Clo xs ⟦d⟧ ρᵣ) Mk-D)
    (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
    (define ℓₐ* (ℓ-with-src ℓₐ lo))
    (match xs
      [(? list?)
       (define ⟦x⟧s : (Listof -⟦e⟧) (for/list ([x (in-list xs)]) (↓ₓ lo x (loc->ℓ (loc 'indy 0 0 (list x))))))
       (define ⟦mon-app⟧
         (let* ([⟦app⟧ (mk-app ℓₐ* (mk-A (list Vᵤ^)) ⟦x⟧s)]
                [⟦rng⟧ (mk-app ℓₐ (mk-V Mk-D) ⟦x⟧s)])
           (mk-mon (ctx-with-ℓ ctx ℓᵣ) ⟦rng⟧ ⟦app⟧)))
       (define ctx* (ctx-neg ctx))
       (define Cₓs (σ@/list Σ (-φ-cache φ) αs))
       (define ⟦mon-x⟧s : (Listof -⟦e⟧)
         (for/list ([Cₓ (in-list Cₓs)] [Vₓ (in-list Vₓs)] [ℓₓ : ℓ (in-list ℓs)])
           (mk-mon (ctx-with-ℓ ctx* ℓₓ) (mk-A (list Cₓ)) (mk-A (list Vₓ)))))
       (match* (xs ⟦x⟧s ⟦mon-x⟧s)
         [('() '() '())
          (⟦mon-app⟧ ρᵣ H φ Σ ⟦k⟧)]
         [((cons x xs*) (cons ⟦x⟧ ⟦x⟧s*) (cons ⟦mon-x⟧ ⟦mon-x⟧s*))
          (define rst : (Listof (Pairof (Listof Symbol) -⟦e⟧))
            (for/list ([xᵢ (in-list xs*)] [⟦mon⟧ᵢ (in-list ⟦mon-x⟧s*)])
              (cons (list xᵢ) ⟦mon⟧ᵢ)))
          (define ⟦k⟧* (let∷ ℓₐ (list x) rst '() ⟦mon-app⟧ ρᵣ ⟦k⟧))
          (⟦mon-x⟧ ρᵣ H φ Σ ⟦k⟧*)])]
      [(-var zs z)
       (error 'app-Indy "TODO: varargs in ->i: ~a" (cons zs z))]))

  (: app-st-p : -𝒾 → -⟦f⟧)
  (define (app-st-p 𝒾)
    (define st-p (-st-p 𝒾))
    (λ (ℓ Vₓs H φ Σ ⟦k⟧)
      (match Vₓs
        [(list _)
         (⟦k⟧ (list (implement-predicate (-Σ-σ Σ) φ st-p Vₓs)) H φ Σ)]
        [_
         (define blm (blm-arity ℓ (show-o st-p) '(1) Vₓs))
         (⟦k⟧ blm H φ Σ)])))

  (: app-st-mk : -𝒾 → -⟦f⟧)
  (define (app-st-mk 𝒾)
    (define st-mk (-st-mk 𝒾))
    (define n (count-struct-fields 𝒾))
    (λ (ℓ Vₓs H φ Σ ⟦k⟧)
      (cond
        [(= n (length Vₓs))
         (define αs (build-list n (λ ([i : Index]) (-α->⟪α⟫ (-α.fld 𝒾 ℓ H i)))))
         (define φ* (alloc* Σ φ αs Vₓs))
         (⟦k⟧ (list {set (-St 𝒾 αs)}) H φ* Σ)]
        [else
         (define blm (blm-arity ℓ (show-o st-mk) n Vₓs))
         (⟦k⟧ blm H φ Σ)])))

  (: app-st-ac : -𝒾 Index → -⟦f⟧)
  (define (app-st-ac 𝒾 i)
    (define ac (-st-ac 𝒾 i))
    (define p  (-st-p 𝒾))
    (define n (count-struct-fields 𝒾))
    
    (: ⟦ac⟧ : -⟦f⟧)
    (define (⟦ac⟧ ℓ Vₓs H φ Σ ⟦k⟧)
      (match Vₓs
        [(list Vₓ^) 
         (define l (ℓ-src ℓ))
         (define (blm) (blm/simp l (show-o ac) (list p) Vₓs ℓ))
         (for/union : (℘ -ς) ([Vₓ (in-set Vₓ^)])
           (match Vₓ
             [(-St 𝒾* αs)
              #:when (𝒾* . substruct? . 𝒾)
              (for/union : (℘ -ς) ([V-φ (in-list (σ@/cache Σ φ (list-ref αs i)))])
                (match-define (cons V^ φ*) V-φ)
                (⟦k⟧ (list V^) H φ* Σ))]
             [(-St* (-St/C _ 𝒾* αℓs) α ctx)
              #:when (𝒾* . substruct? . 𝒾)
              (define V^  (σ@ Σ (-φ-cache φ) α))
              (cond
                ;; mutable field should be wrapped
                [(struct-mutable? 𝒾 i)
                 (match-define (-⟪α⟫ℓ αᵢ ℓᵢ) (list-ref αℓs i))
                 (define Cᵢ^ (σ@ Σ (-φ-cache φ) αᵢ))
                 (⟦ac⟧ ℓ (list V^) H φ Σ (mon.c∷ (ctx-with-ℓ ctx ℓᵢ) Cᵢ^ ⟦k⟧))]
                ;; no need to check immutable field
                [else
                 ;; TODO: could this loop forever due to cycle?
                 (⟦ac⟧ ℓ (list V^) H φ Σ ⟦k⟧)])]
             [(or (-● ps)
                  (and (? -t?)
                       (app (λ ([t : -t]) (hash-ref (-φ-condition φ) (list t) mk-∅)) ps)))
              #:when ps
              (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ (-Σ-σ Σ) φ p {set Vₓ})]) : -ς
                #:true (let ([Vₐ
                              (if (-t? Vₓ)
                                  (-t.@ ac (list Vₓ))
                                  (let ([psₐ (if (and (equal? 𝒾 -𝒾-cons) (equal? i 1) (∋ ps 'list?))
                                                 {set 'list?}
                                                 ∅)])
                                    (-● psₐ)))])
                         (⟦k⟧ (list {set Vₐ}) H φ₁ Σ)) 
                #:false (⟦k⟧ (blm) H φ₂ Σ))]
             [_ (⟦k⟧ (blm) H φ Σ)]))]
        [_
         (define blm (blm-arity ℓ (show-o ac) 1 Vₓs))
         (⟦k⟧ blm H φ Σ)]))
    ⟦ac⟧)

  (: app-st-mut : -𝒾 Index → -⟦f⟧)
  (define (app-st-mut 𝒾 i)
    (define mut (-st-mut 𝒾 i))
    (define p (-st-p 𝒾))
    
    (: ⟦mut⟧ : -⟦f⟧)
    (define (⟦mut⟧ ℓ Vₓs H φ Σ ⟦k⟧)
      (match Vₓs
        [(list Vₛ^ Vᵥ^)
         (define l (ℓ-src ℓ))
         (define (blm) (blm/simp l (show-o mut) (list p) (list Vₛ^) ℓ))
         (for/union : (℘ -ς) ([Vₛ (in-set Vₛ^)])
           (match Vₛ
             [(-St 𝒾* αs)
              #:when (𝒾* . substruct? . 𝒾)
              (define φ* (mut! Σ φ (list-ref αs i) Vᵥ^))
              (⟦k⟧ (list {set -void}) H φ* Σ)]
             [(-St* (-St/C _ 𝒾* γℓs) α ctx)
              #:when (𝒾* . substruct? . 𝒾)
              (define ctx* (ctx-neg ctx))
              (match-define (-⟪α⟫ℓ γᵢ ℓᵢ) (list-ref γℓs i))
              (define Vₛ* (σ@ Σ (-φ-cache φ) α))
              (define ⟦k⟧* (ap∷ (list Vₛ* {set mut}) '() ⊥ρ ℓ ⟦k⟧))
              (define Cᵢ^ (σ@ Σ (-φ-cache φ) γᵢ))
              (push-mon (ctx-with-ℓ ctx* ℓᵢ) Cᵢ^ Vᵥ^ H φ Σ ⟦k⟧*)]
             [(or (? integer?) (? -●?))
              (with-φ+/- ([(φ₁ φ₂) (φ+/-pV^ (-Σ-σ Σ) φ p {set Vₛ})]) : -ς
                #:true  (let ([φ* (add-leak! '† Σ φ₁ Vᵥ^)])
                          (⟦k⟧ (list {set -void}) H φ* Σ))
                #:false (⟦k⟧ (blm) H φ₂ Σ))]
             [_ (⟦k⟧ (blm) H φ Σ)]))]
        [_
         (define blm (blm-arity ℓ (show-o mut) 2 Vₓs))
         (⟦k⟧ blm H φ Σ)]))
    ⟦mut⟧)

  ;; FIXME tmp hack for `make-sequence` use internallyr
  (: app-make-sequence : -⟦f⟧)
  (define app-make-sequence
    (let ([A (map (inst set -V) (list -car -cdr 'values -one -cons? -ff -ff))])
      (λ (ℓ Vₓs H φ Σ ⟦k⟧)
        (⟦k⟧ A H φ Σ))))

  (: app-opq : -V → -⟦f⟧)
  (define (app-opq Vₕ)
    (λ (ℓ Vs H φ Σ ⟦k⟧)
      (define tag
        (match Vₕ
          [(-Fn● _ t) t]
          [_ '†]))
      (define φ*
        (for/fold ([φ : -φ φ]) ([V (in-list Vs)])
          (add-leak! tag Σ φ V)))
      (define αₖ (-αₖ H (-HV tag) φ*))
      (define ⟦k⟧* (bgn0.e∷ (list {set (-● ∅)}) '() ⊥ρ ⟦k⟧))
      {set (-ς↑ (σₖ+! Σ αₖ ⟦k⟧*))}))

  (: app/rest/unsafe : ℓ -V (Listof -V^) -V -H -φ -Σ -⟦k⟧ → (℘ -ς))
  ;; Apply function with (in general, part of) rest arguments already allocated,
  ;; assuming that init/rest args are already checked to be compatible.
  (define (app/rest/unsafe ℓ V-func V-inits V-rest H φ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (define num-inits (length V-inits))
    (define arg-counts
      (for/set: : (℘ Arity) ([a (estimate-list-lengths σ (-φ-cache φ) V-rest)] #:when a)
        (match a
          [(? exact-nonnegative-integer? n) (+ num-inits n)]
          [(arity-at-least n) (arity-at-least (+ num-inits n))])))
    
    (: app-prim/rest : -o → (℘ -ς))
    (define (app-prim/rest o)
      (define V-rests (unalloc σ (-φ-cache φ) V-rest))
      (for/union : (℘ -ς) ([Vᵣs (in-set V-rests)])
        (app₁ ℓ o (append V-inits Vᵣs) H φ Σ ⟦k⟧)))

    (: app-clo/rest : -formals -⟦e⟧ -ρ → (℘ -ς))
    (define (app-clo/rest xs ⟦e⟧ ρ)
      (match xs
        ;; TODO: if we assume clo as rest-arg, this path may never be reached...
        [(? list? xs)
         (define n (length xs))
         (define num-remaining-inits (- n num-inits))
         (define Vᵣ-lists
           (for/set: : (℘ (Listof -V^)) ([Vᵣ-list (in-set (unalloc σ (-φ-cache φ) V-rest))]
                                         #:when (= num-remaining-inits (length Vᵣ-list)))
             Vᵣ-list))
         (for/union : (℘ -ς) ([Vᵣs Vᵣ-lists])
           ((app-clo xs ⟦e⟧ ρ) ℓ (append V-inits Vᵣs) H φ Σ ⟦k⟧))]
        [(-var zs z)
         (define n (length zs))
         (define num-remaining-inits (- n num-inits))

         (: app/adjusted-args : -φ (Listof -V^) -V → (℘ -ς))
         (define (app/adjusted-args φ V-inits V-rest)
           (define-values (ρ₁ φ₁) (bind-args Σ ρ ℓ H φ zs V-inits))
           (define αᵣ (-α->⟪α⟫ (-α.x z H)))
           (define ρ₂ (ρ+ ρ₁ z αᵣ))
           (define φ₂ (alloc Σ φ₁ αᵣ {set V-rest}))
           (⟦e⟧ ρ₂ H φ₂ Σ ⟦k⟧))
         
         (cond
           ;; Need to retrieve some more arguments from `V-rest` as part of inits
           [(<= 0 num-remaining-inits)
            (define pairs (unalloc-prefix σ (-φ-cache φ) V-rest num-remaining-inits))
            (for/union : (℘ -ς) ([pair (in-set pairs)])
              (match-define (cons V-init-more Vᵣ) pair)
              (define V-inits* (append V-inits V-init-more))
              (app/adjusted-args φ V-inits* Vᵣ))]
           ;; Need to allocate some init arguments as part of rest-args
           [else
            (define-values (V-inits* V-inits.rest) (split-at V-inits n))
            (define-values (V-rest* φ*) (alloc-rest-args Σ ℓ H φ V-inits.rest #:end V-rest))
            (app/adjusted-args φ* V-inits* V-rest*)])]))

    (: app-Ar/rest : -=>_ ⟪α⟫ -ctx → (℘ -ς))
    (define (app-Ar/rest C α ctx)
      (define Vᵤ^ (σ@ σ (-φ-cache φ) α))
      (match C
        [(-=> (-var αℓs₀ (-⟪α⟫ℓ αᵣ ℓᵣ)) _)
         (define n (length αℓs₀))
         (define num-remaining-inits (- n num-inits))
         (cond
           ;; Need to retrieve some more arguments from `V-rest` as part of inits
           [(<= 0 num-remaining-inits)
            (define pairs (unalloc-prefix σ (-φ-cache φ) V-rest num-remaining-inits))
            (for/union : (℘ -ς) ([unalloced (in-set pairs)])
              (match-define (cons V-init-more Vᵣ*) unalloced)
              (define V-inits* (append V-inits V-init-more))
              ((apply-app-Ar C Vᵤ^ ctx) ℓ V-inits* Vᵣ* H φ Σ ⟦k⟧))]
           ;; Need to allocate some init arguments as part of rest-args
           [else
            (define-values (V-inits* V-inits.rest) (split-at V-inits n))
            (define-values (Vᵣ* φ*) (alloc-rest-args Σ ℓ H φ V-inits.rest #:end V-rest))
            ((apply-app-Ar C Vᵤ^ ctx) ℓ V-inits* Vᵣ* H φ Σ ⟦k⟧)])]
        [(-=> (? list? αℓₓs) _)
         (define n (length αℓₓs))
         (define num-remaining-args (- n num-inits))
         (cond
           [(>= num-remaining-args 0)
            (define pairs (unalloc-prefix σ (-φ-cache φ) V-rest num-remaining-args))
            (for/union : (℘ -ς) ([unalloced (in-set pairs)])
              (match-define (cons V-inits-more _) unalloced)
              (define V-inits* (append V-inits V-inits-more))
              ((app-Ar C Vᵤ^ ctx) ℓ V-inits* H φ Σ ⟦k⟧))]
           [else
            (error 'app/rest "expect ~a arguments, given ~a: ~a" n num-inits V-inits)])]
        [(-∀/C xs ⟦c⟧ ρ)
         (define l-seal (-ctx-neg ctx))
         (define-values (ρ* φ*)
           (for/fold ([ρ : -ρ ρ] [φ : -φ φ]) ([x (in-list xs)])
             (define αₛ (-α->⟪α⟫ (-α.imm (-Seal/C x H l-seal))))
             (define αᵥ (-α->⟪α⟫ (-α.sealed x H)))
             (values (ρ+ ρ x αₛ) (alloc Σ φ αᵥ ∅))))
         (define ⟦init⟧s : (Listof -⟦e⟧) (for/list ([V^ (in-list V-inits)]) (mk-A (list V^))))
         (define ⟦k⟧* (mon.v∷ ctx Vᵤ^ (ap∷ (list {set 'apply}) `(,@⟦init⟧s ,(mk-V V-rest)) ⊥ρ ℓ ⟦k⟧)))
         (⟦c⟧ ρ* H φ* Σ ⟦k⟧*)]
        [(-Case-> cases)
         (cond
           [(and (= 1 (set-count arg-counts)) (integer? (set-first arg-counts)))
            (define n (set-first arg-counts))
            (assert
             (for/or : (Option (℘ -ς)) ([C cases] #:when (arity-includes? (guard-arity C) n))
               (app-Ar/rest C α ctx)))]
           [else
            (for*/union : (℘ -ς) ([C cases]
                                  [a (in-value (guard-arity C))]
                                  #:when (for/or : Boolean ([argc (in-set arg-counts)])
                                           (arity-includes? a argc)))
              (app-Ar/rest C α ctx))])]))
    
    (match V-func
      [(-Clo xs ⟦e⟧ ρ) (app-clo/rest xs ⟦e⟧ ρ)]
      [(-Case-Clo cases)
       (define (go-case [clo : -Clo]) : (℘ -ς)
         (match-define (-Clo xs ⟦e⟧ ρ) clo)
         (app-clo/rest xs ⟦e⟧ ρ))
       (cond
         [(and (= 1 (set-count arg-counts)) (integer? (set-first arg-counts)))
          (define n (set-first arg-counts))
          ;; already handled arity mismatch
          (assert
           (for/or : (Option (℘ -ς)) ([clo (in-list cases)]
                                      #:when (arity-includes? (assert (V-arity clo)) n))
             (go-case clo)))]
         [else
          (for*/union : (℘ -ς) ([clo (in-list cases)]
                                [a (in-value (assert (V-arity clo)))]
                                #:when (for/or : Boolean ([argc (in-set arg-counts)])
                                         (arity-includes? a argc)))
                      (go-case clo))])]
      [(-Ar C α ctx) (app-Ar/rest C α ctx)]
      [(? -o? o) (app-prim/rest o)]
      [_ (error 'app/rest "unhandled: ~a" (show-V V-func))]))
  )
