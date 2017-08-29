#lang typed/racket/base

(require racket/match
         racket/set
         racket/string
         racket/splicing
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt"
         )

(provide pretty-print@)
(define-unit pretty-print@
  (import ast-pretty-print^ env^)
  (export pretty-print^)

  (define (show-ς [ς : -ς]) : Sexp
    (match ς
      [(-ς↑ αₖ      ) (show-αₖ αₖ)]
      [(-ς↓ αₖ $ Γ A) `(rt: ,(show-αₖ αₖ) ,(show-A A) ‖ ,@(show-Γ Γ))]))

  (define (show-σ [σ : -σ])
    (for*/list : (Listof Sexp) ([(⟪α⟫ᵢ Vs) (in-hash σ)]
                                [α (in-value (⟪α⟫->-α (cast #|FIXME TR|# ⟪α⟫ᵢ ⟪α⟫)))])
      `(,(show-⟪α⟫ (cast #|FIXME TR|# ⟪α⟫ᵢ ⟪α⟫)) ↦ ,@(set-map Vs show-V))))

  (define (show-h [h : -h]) : Sexp
    (match h
      [(? -t?) (show-t h)]
      [(? -o?) (show-o h)]
      [(? -αₖ?) (show-αₖ h)]
      [(? -V? V) (show-V V)]
      [(-st/c.mk 𝒾) (format-symbol "~a/c" (-𝒾-name 𝒾))]
      [(-st/c.ac 𝒾 i) (format-symbol "~a/c._~a" (-𝒾-name 𝒾) (n-sub i))]
      [(-->i.mk) '-->i]
      [(-->i.dom i) (format-symbol "-->i._~a" (n-sub i))]
      [(-->i.rng) '-->i.rng]
      [(-->.mk) '-->]
      [(-->*.mk) '-->*]
      [(-->.dom i) (format-symbol "-->._~a" (n-sub i))]
      [(-->.rst) '-->.rest]
      [(-->.rng) '-->.rng]
      [(-ar.mk) 'arr]
      [(-ar.ctc) 'arr.ctc]
      [(-ar.fun) 'arr.fun]
      [(-values.ac i) (format-symbol "values._~a" (n-sub i))]
      [(-≥/c b) `(≥/c ,(show-b b))]
      [(-≤/c b) `(≤/c ,(show-b b))]
      [(->/c b) `(>/c ,(show-b b))]
      [(-</c b) `(</c ,(show-b b))]
      [(-≡/c b) `(≡/c ,(show-b b))]
      [(-≢/c b) `(≢/c ,(show-b b))]
      [(-not/c o) `(not/c ,(show-o o))]
      [(-clo ⟦e⟧) `(λ∈ ,(show-⟦e⟧ ⟦e⟧))]))

  (define (show-t [?t : -?t]) : Sexp
    (match ?t
      [#f '∅]
      [(? integer? i) (show-ℓ (cast i ℓ))]
      [(-t.x x) x]
      [(-𝒾 x _) x]
      [(? -e? e) (show-e e)]
      [(-t.@ h ts) `(@ ,(show-h h) ,@(map show-t ts))]))

  (define (show-Γ [Γ : -Γ]) : (Listof Sexp)
    (set-map Γ show-t))

  (define (show-δ$ [δ$ : -δ$]) : (Listof Sexp)
    (for/list : (Listof Sexp) ([(l t) (in-hash δ$)])
      `(,(show-loc l) ↦ ,(show-t t))))

  (define show-$ : (-$ → (Listof Sexp)) show-δ$)

  (define (show-σₖ [σₖ : -σₖ]) : (Listof Sexp)
    (for/list ([(αₖ κs) σₖ])
      `(,(show-αₖ αₖ) ↦ ,@(set-map κs show-κ))))

  (define show-blm-reason : ((U -V -v -h) → Sexp)
    (match-lambda
      [(? -V? V) (show-V V)]
      [(? -v? v) (show-e v)]
      [(? -h? h) (show-h h)]))

  (define (show-V [V : -V]) : Sexp
    (match V
      [(-b b) (show-b b)]
      [(-● ps)
       (string->symbol
        (string-join
         (for/list : (Listof String) ([p ps])
           (format "_~a" (show-h p)))
         ""
         #:before-first "●"))]
      [(? -o? o) (show-o o)]
      [(-Clo xs ⟦e⟧ ρ Γ) `(λ ,(show-formals xs) ,(show-⟦e⟧ ⟦e⟧) ‖ ,(show-ρ ρ) ‖ ,@(show-Γ Γ))]
      [(-Case-Clo clauses ρ Γ)
       `(case-lambda
          ,@(for/list : (Listof Sexp) ([clause clauses])
              (match-define (cons xs _) clause)
              `(,xs …)))]
      [(-Fn● arity)
       (string->symbol (format "Fn●_~a" arity))]
      [(-Ar guard α _)
       (match α
         [(? -𝒾? 𝒾) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
         [(-α.wrp 𝒾) (format-symbol "⟪~a⟫" (-𝒾-name 𝒾))]
         [_ `(,(show-V guard) ◃ ,(show-⟪α⟫ α))])]
      [(-St 𝒾 αs) `(,(-𝒾-name 𝒾) ,@(map show-⟪α⟫ αs))]
      [(-St* (-St/C _ 𝒾 γℓs) α _)
       `(,(format-symbol "~a/wrapped" (-𝒾-name 𝒾))
         ,@(for/list : (Listof Sexp) ([γℓ γℓs]) (if γℓ (show-⟪α⟫ℓ γℓ) '✓))
         ▹ ,(show-⟪α⟫ α))]
      [(-Vector αs) `(vector ,@(map show-⟪α⟫ αs))]
      [(-Vector^ α n) `(vector^ ,(show-⟪α⟫ α) ,(show-V n))]
      [(-Hash^ k v im?) `(,(if im? 'hash^ 'mutable-hash^) ,(show-⟪α⟫ k) ,(show-⟪α⟫ v))]
      [(-Set^ elems im?) `(,(if im? 'set^ 'mutable-set^) ,(show-⟪α⟫ elems))]
      [(-Hash/guard C α _) `(hash/guard ,(show-V C) ,(show-⟪α⟫ α))]
      [(-Set/guard C α _) `(set/guard ,(show-V C) ,(show-⟪α⟫ α))]
      [(-Vector/guard grd _ _)
       (match grd
         [(-Vector/C γs) `(vector/diff ,@(map show-⟪α⟫ℓ γs))]
         [(-Vectorof γ) `(vector/same ,(show-⟪α⟫ℓ γ))])]
      [(-And/C _ l r) `(and/c ,(show-⟪α⟫ (-⟪α⟫ℓ-addr l)) ,(show-⟪α⟫ (-⟪α⟫ℓ-addr r)))]
      [(-Or/C _ l r) `(or/c ,(show-⟪α⟫ (-⟪α⟫ℓ-addr l)) ,(show-⟪α⟫ (-⟪α⟫ℓ-addr r)))]
      [(-Not/C γ) `(not/c ,(show-⟪α⟫ (-⟪α⟫ℓ-addr γ)))]
      [(-One-Of/C vs) `(one-of/c ,@(set-map vs show-b))]
      [(-Vectorof γ) `(vectorof ,(show-⟪α⟫ (-⟪α⟫ℓ-addr γ)))]
      [(-Vector/C γs) `(vector/c ,@(map show-⟪α⟫ (map -⟪α⟫ℓ-addr γs)))]
      [(-Hash/C k v) `(hash/c ,(show-⟪α⟫ (-⟪α⟫ℓ-addr k)) ,(show-⟪α⟫ (-⟪α⟫ℓ-addr v)))]
      [(-Set/C elems) `(set/c ,(show-⟪α⟫ (-⟪α⟫ℓ-addr elems)))]
      [(-=> αs βs _)
       (define show-rng
         (cond [(list? βs) (show-⟪α⟫ℓs βs)]
               [else 'any]))
       (match αs
         [(-var αs α) `(,(map show-⟪α⟫ℓ αs) #:rest ,(show-⟪α⟫ℓ α) . ->* . ,show-rng)]
         [(? list? αs) `(,@(map show-⟪α⟫ℓ αs) . -> . ,show-rng)])]
      [(-=>i γs (list (-Clo _ ⟦e⟧ _ _) (-λ xs d) _) _)
       `(->i ,@(map show-⟪α⟫ℓ γs)
             ,(match xs
                [(? list? xs) `(res ,xs ,(show-e d))]
                [_ (show-e d)]))]
      [(-Case-> cases _)
       `(case->
         ,@(for/list : (Listof Sexp) ([kase cases])
             (match-define (cons αs β) kase)
             `(,@(map show-⟪α⟫ αs) . -> . ,(show-⟪α⟫ β))))]
      [(-St/C _ 𝒾 αs)
       `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(map show-⟪α⟫ (map -⟪α⟫ℓ-addr αs)))]
      [(-x/C ⟪α⟫) `(recursive-contract ,(show-⟪α⟫ ⟪α⟫))]
      [(-∀/C xs ⟦c⟧ ρ) `(∀/C ,xs ,(show-⟦e⟧ ⟦c⟧))]
      [(-Seal/C α _) (format-symbol "(seal/c ~a)" (assert (show-⟪α⟫ α) symbol?))]
      [(-Sealed α) (format-symbol "sealed@~a" (assert (show-⟪α⟫ α) symbol?))]))

  (define (show-⟪α⟫ℓ [⟪α⟫ℓ : -⟪α⟫ℓ]) : Symbol
    (match-define (-⟪α⟫ℓ ⟪α⟫ ℓ) ⟪α⟫ℓ)
    (define α (⟪α⟫->-α ⟪α⟫))
    (string->symbol
     (format "~a~a" (if (-e? α) (show-e α) (show-⟪α⟫ ⟪α⟫)) (n-sup ℓ))))

  (: show-⟪α⟫ℓs : (Listof -⟪α⟫ℓ) → Sexp)
  (define show-⟪α⟫ℓs (show-values-lift show-⟪α⟫ℓ))

  (define (show-ΓA [ΓA : -ΓA]) : Sexp
    (match-define (-ΓA Γ A) ΓA)
    `(,(show-A A) ‖ ,@(set-map Γ show-t)))

  (define (show-A [A : -A])
    (cond [(-W? A) (show-W A)]
          [else (show-blm A)]))

  (define (show-W [W : -W]) : Sexp
    (match-define (-W Vs t) W)
    `(,@(map show-V Vs) @ ,(show-t t)))

  (define (show-W¹ [W : -W¹]) : Sexp
    (match-define (-W¹ V t) W)
    `(,(show-V V) @ ,(show-t t)))

  (define (show-blm [blm : -blm]) : Sexp
    (match-define (-blm l+ lo Cs Vs ℓ) blm)
    (match* (Cs Vs)
      [('() (list (-b (? string? msg)))) `(error ,msg)] ;; HACK
      [(_ _) `(blame ,l+ ,lo ,(map show-blm-reason Cs) ,(map show-V Vs) ,(show-ℓ ℓ))]))


  (splicing-local
      ((define ⟦e⟧->e : (HashTable -⟦e⟧ -e) (make-hasheq)))
    
    (: remember-e! : -e -⟦e⟧ → -⟦e⟧)
    (define (remember-e! e ⟦e⟧)
      (define ?e₀ (recall-e ⟦e⟧))
      (when (and ?e₀ (not (equal? ?e₀ e)))
        (error 'remember-e! "already mapped to ~a, given ~a" (show-e ?e₀) (show-e e)))
      (hash-set! ⟦e⟧->e ⟦e⟧ e)
      ⟦e⟧)

    (: recall-e : -⟦e⟧ → (Option -e))
    (define (recall-e ⟦e⟧) (hash-ref ⟦e⟧->e ⟦e⟧ #f))
    
    (define show-⟦e⟧ : (-⟦e⟧ → Sexp)
      (let-values ([(⟦e⟧->symbol symbol->⟦e⟧ _) ((inst unique-sym -⟦e⟧) '⟦e⟧)])
        (λ (⟦e⟧)
          (cond [(recall-e ⟦e⟧) => show-e]
                [else (⟦e⟧->symbol ⟦e⟧)])))))

  (define (show-αₖ [αₖ : -αₖ]) : Sexp
    (cond [(-ℬ? αₖ) (show-ℬ αₖ)]
          [(-ℳ? αₖ) (show-ℳ αₖ)]
          [(-ℱ? αₖ) (show-ℱ αₖ)]
          [(-ℋ𝒱? αₖ) (format-symbol "ℋ𝒱_~a" (n-sub (-αₖ-ctx αₖ)))]
          [else     (error 'show-αₖ "~a" αₖ)]))

  (define (show-ℬ [ℬ : -ℬ]) : Sexp
    (match-define (-ℬ _ _ xs ⟦e⟧ ρ _) ℬ)
    (match xs
      ['() `(ℬ ()                 ,(show-⟦e⟧ ⟦e⟧) ,(show-ρ ρ))]
      [_   `(ℬ ,(show-formals xs) …               ,(show-ρ ρ))]))

  (define (show-ℳ [ℳ : -ℳ]) : Sexp
    (match-define (-ℳ $ ⟪ℋ⟫ ctx C V Γ) ℳ)
    `(ℳ ,(show-⟪ℋ⟫ ⟪ℋ⟫) ,(show-W¹ C) ,(show-W¹ V) ‖ ,@(show-Γ Γ) ‖ ,@(show-$ $)))

  (define (show-ℱ [ℱ : -ℱ]) : Sexp
    (match-define (-ℱ _ _ l ℓ C V _) ℱ)
    `(ℱ ,(show-W¹ C) ,(show-W¹ V)))

  (define-parameter verbose? : Boolean #f)

  (define (show-⟪ℋ⟫ [⟪ℋ⟫ : -⟪ℋ⟫]) : Sexp
    (if (verbose?)
        (show-ℋ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫))
        ⟪ℋ⟫))
  (define (show-ℋ [ℋ : -ℋ]) : (Listof Sexp) (map show-edge ℋ))

  (: show-edge : -edge → Sexp)
  (define (show-edge edge)
    (match-define (-edge tgt ℓ) edge)
    `(,(show-ℓ ℓ) ↝ ,(show-tgt tgt)))

  (: show-tgt : -edge.tgt → Sexp)
  (define (show-tgt tgt)
    (cond
      [(-o? tgt) (show-o tgt)]
      [(set? tgt) `(one-of/c ,@(set-map tgt show-b))]
      [(list? tgt) (for/list : (Listof Sexp) ([x (in-list tgt)])
                     (cond [(symbol? x) x]
                           [(ℓ? x) (show-ℓ x)]
                           [(-t? x) (show-t x)]
                           [(not x) '⊘]
                           [else (show-⟦e⟧ x)]))]
      [else (show-⟦e⟧ tgt)]))

  (define (show-⟪α⟫ [⟪α⟫ : ⟪α⟫]) : Sexp

    (define (show-α.x [x : Symbol] [⟪ℋ⟫ : -⟪ℋ⟫])
      (format-symbol "~a_~a" x (n-sub ⟪ℋ⟫)))

    (define α (⟪α⟫->-α ⟪α⟫))
    (match (⟪α⟫->-α ⟪α⟫)
      [(-α.x x ⟪ℋ⟫) (show-α.x x ⟪ℋ⟫)]
      [(-α.hv) 'αₕᵥ]
      [(-α.mon-x/c x ⟪ℋ⟫ _) (show-α.x x ⟪ℋ⟫)]
      [(-α.fc-x/c x ⟪ℋ⟫) (show-α.x x ⟪ℋ⟫)]
      [(-α.fv ⟪ℋ⟫) (show-α.x 'dummy ⟪ℋ⟫)]
      [(-𝒾 x _) x]
      [(-α.wrp (-𝒾 x _)) (format-symbol "⟨~a⟩" x)]
      [(-α.sealed x ⟪ℋ⟫) (format-symbol "~a*" (show-α.x x ⟪ℋ⟫))]
      [(? -e? e) (show-e e)]
      [_ (format-symbol "α~a" (n-sub ⟪α⟫))]))

  (define (show-ρ [ρ : -ρ]) : (Listof Sexp)
    (for/list ([(x ⟪α⟫ₓ) ρ] #:unless (equal? x -x-dummy))
      `(,x ↦ ,(show-⟪α⟫ (cast #|FIXME TR|# ⟪α⟫ₓ ⟪α⟫)))))

  (define show-loc : (-loc → Sexp)
    (match-lambda
      [(? symbol? s) s]
      [(-𝒾 x _) x]
      [(-loc.offset 𝒾 i t) `(,(show-t t) ↪ ,(show-ac (if (-𝒾? 𝒾) 𝒾 (-𝒾 𝒾 'Λ)) i))]))

  (: show-M : -M → (Listof Sexp))
  (define (show-M M)
    (for/list ([(α As) (in-hash M)])
      `(,(show-αₖ α) ↦ ,(set-map As show-ΓA))))

  (: show-κ : -κ → Sexp)
  (define (show-κ κ)
    (match κ
      [(-κ.rt _ dom Γ t looped?)
       `(,(show-t t) ,(set->list dom) ,(show-Γ Γ) ,looped?)]
      [(-κ _)
       `κ]))
  )
