#lang typed/racket/base

(provide pretty-print@)

(require typed/racket/unit
         racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/string
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt"
         )

(define-unit pretty-print@
  (import ast-pretty-print^)
  (export pretty-print^)

  #;(: show-Ξ : Sexp)
  #;(define show-Ξ : (Ξ → Sexp)
      (match-lambda
        [(Ξ:co K α H) `(,(show-K) ,(show-αₖ α) ,H)]
        [(? Blm? b) (show-Blm b)]))

  (: show-map (∀ (X Y X* Y*) (X → X*) (Y → Y*) → (HashTable X Y) → (Listof (List X* '↦ Y*))))
  (define ((show-map show-k show-v) m)
    (for/list ([(k v) (in-hash m)]) `(,(show-k k) ↦ ,(show-v v)))) 

  #;(define (show-h [h : -h]) : Sexp
      (match h
        [(? -t?) (show-t h)]
        [(? -o?) (show-o h)]
        [(? -αₖ?) (show-αₖ h)]
        [(-≥/c b) `(≥/c ,(show-t b))]
        [(-≤/c b) `(≤/c ,(show-t b))]
        [(->/c b) `(>/c ,(show-t b))]
        [(-</c b) `(</c ,(show-t b))]
        [(-≡/c b) `(≡/c ,(show-t b))]
        [(-not/c h) `(not/c ,(show-h h))]
        [(-arity-includes/c a) `(arity-includes/c ,(show-b a))]))

  #;(define show-t : (-t → Sexp)
      (match-lambda
        [(? integer? i) (format-symbol "•~a" (n-sub i))]
        [(-b b) (show-b b)]
        [(-t.@ h ts) `(,(show-o h) ,@(map show-t ts))]))

  #;(define (show-Γ [Γ : -Γ])
      (for*/list : (Listof Sexp) ([(t ps) (in-hash Γ)])
        `(,(show-t t) ∈ ,@(set-map ps show-h))))

  

  (define show-blm-reason : ((U V P V^) → Sexp)
    (match-lambda
      [(? V? V) (show-V V)]
      [(? P? P) (show-P P)]
      [(? set? s) (show-T s)]))

  (define (show-V [V : V]) : Sexp
    (match V
      [(-b b) (show-b b)]
      [(-● ps)
       (string->symbol
        (string-join
         (for/list : (Listof String) ([p ps])
           (format "_~a" (show-P p)))
         ""
         #:before-first "●"))]
      [(? -o? o) (show-o o)]
      [(Clo xs ⟦E⟧ Ρ) `(λ ,(show-formals xs) … ,(show-Ρ Ρ))]
      [(Case-Clo cases) `(case-lambda ,@(map show-V cases))]
      [(X/G _ G α) `(,(show-V G) ◃ ,(show-α α))]
      [(St 𝒾 αs) `(,(-𝒾-name 𝒾) ,@(map show-α αs))]
      [(Vect αs) `(vector ,@(map show-α αs))]
      [(Vect^ α n) `(vector^ ,(show-α α) ,(show-T n))]
      [(Hash^ k v im?) `(,(if im? 'hash^ 'mutable-hash^) ,(show-α k) ,(show-α v))]
      [(Set^ elems im?) `(,(if im? 'set^ 'mutable-set^) ,(show-α elems))]
      [(And/C _ l r) `(and/c ,(show-α (αℓ-_0 l)) ,(show-α (αℓ-_0 r)))]
      [(Or/C _ l r) `(or/c ,(show-α (αℓ-_0 l)) ,(show-α (αℓ-_0 r)))]
      [(Not/C γ) `(not/c ,(show-α (αℓ-_0 γ)))]
      [(One-Of/C vs) `(one-of/c ,@(map show-b vs))]
      [(Vectof γ) `(vectorof ,(show-α (αℓ-_0 γ)))]
      [(Vect/C γs) `(vector/c ,@(map show-α (map αℓ-_0 γs)))]
      [(Hash/C k v) `(hash/c ,(show-α (αℓ-_0 k)) ,(show-α (αℓ-_0 v)))]
      [(Set/C elems) `(set/c ,(show-α (αℓ-_0 elems)))]
      [(==> (-var αℓs αℓᵣ) βs)
       (define show-rng (if βs (show-αℓs βs) 'any))
       (cond [αℓᵣ `(,(map show-αℓ αℓs) #:rest ,(show-αℓ αℓᵣ) . ->* . ,show-rng)]
             [else `(,@(map show-αℓ αℓs) . -> . ,show-rng)])]
      [(==>i Doms Rng)
       `(->i ,(map show-Dom Doms) ,(show-Dom Rng))]
      [(Case-=> cases) `(case-> ,@(map show-V cases))]
      [(St/C _ 𝒾 αs) `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(map show-α (map αℓ-_0 αs)))]
      [(X/C α) `(recursive-contract ,(show-α α))]
      [(∀/C xs ⟦C⟧ Ρ) `(∀/C ,xs …)]
      [(Seal/C x H _) (format-symbol "(seal/c ~a_~a)" x (n-sub H))]
      [(Sealed α) (format-symbol "sealed@~a" (assert (show-α α) symbol?))] 
      #;[(? -t? t) (show-t t)]
      #;[(? -h? h) (show-h h)]))

  (define show-Dom : (Dom → (Listof Sexp))
    (match-lambda
      [(Dom x (Clo (-var xs #f) ⟦E⟧ _) _) `(,x ,xs …)]
      [(Dom x (? integer? α₀)         _) `(,x ,(show-α (cast α₀ α)))]))

  (define show-⟦dom⟧ : (⟦dom⟧ → (Listof Sexp))
    (match-lambda
      [(⟦dom⟧ x ?xs ⟦C⟧ _) (if ?xs `(,x ,?xs …) `(,x …))]))

  (define show-αℓ : (αℓ → Symbol)
    (match-lambda
      [(αℓ α ℓ)
       (define -α (inspect-α α))
       (string->symbol
        (format "~a~a" (if (-e? -α) (show-e -α) (show-α α)) (n-sup ℓ)))]))

  (: show-αℓs : (Listof αℓ) → Sexp)
  (define show-αℓs (show-values-lift show-αℓ))

  (define (show-T [T : (U T T^)]) : Sexp
    (cond [(set? T) (set-map T show-V)]
          [(S? T) (show-S T)]
          [else (show-V T)]))

  (define show-S : (S → Sexp)
    (match-lambda
      [(-b b) (show-b b)]
      [(? -o? o) (show-o o)]
      [(S:α α) (show-α α)]
      [(S:@ S Ss) `(,(show-S S) ,@(map show-S Ss))]))

  (define (show-Blm [blm : Blm]) : Sexp
    (match-define (Blm ℓ lo Cs Vs) blm)
    (match* (Cs Vs)
      [('() (list (-b (? string? msg)))) `(error ,msg)] ;; HACK
      [(_ _) `(blame ,(show-ℓ ℓ) ,lo ,(map show-blm-reason Cs) ,(map show-T Vs))]))

  (define show-αₖ : (αₖ → Sexp)
    (match-lambda
      [(αₖ:exp ⟦E⟧ Ρ) `(αₖ … ,(show-Ρ Ρ))]
      [(αₖ:mon ctx α) `(mon ,(Ctx-pos ctx) ,α)]
      [(αₖ:fc ℓ α) `(fc ,(ℓ-src ℓ) ,α)]
      [(αₖ:hv tag) tag]
      [(αₖ:term/c α W) `(term/c ,(show-α α) ,@(map show-T W))]))

  (: show-α : α → Sexp)
  (define (show-α α)
    (define (show-α:x [x : Symbol] [H : H]) (format-symbol "~a~a" x (n-sub H)))
    (match (inspect-α α)
      [(-α:x x H) (show-α:x x H)]
      [(-α:hv l)
       (cond [l (format-symbol "αₕᵥ_~a_~a" (car l) (cdr l))]
             [else 'αₕᵥ])]
      [(-α:mon-x/c x H _) (show-α:x x H)]
      [(-α:fc-x/c x H) (show-α:x x H)]
      [(-α:dummy H) (show-α:x 'dummy H)]
      [(-α:top (-𝒾 x _)) x]
      [(-α:wrp (-𝒾 x _)) (format-symbol "⟨~a⟩" x)]
      [(-α:sealed x H) (format-symbol "~a*" (show-α:x x H))]
      [(-α:imm V) (show-V V)]
      [(-α:imm:listof x C _) (string->symbol (format "(listof ~a)" (show-V C)))]
      [(-α:imm:ref-listof x C _) (string->symbol (format "(ref ~a)" x))]
      [_ (format-symbol "α~a" (n-sub α))]))

  

  (: dump-Σᵥ ([Σᵥ] [#:tag Any #:appendix? Boolean] . ->* . Void))
  (define (dump-Σᵥ Σᵥ #:tag [tag 'store] #:appendix? [appendix? #f])
    (printf "~a:~n" tag)
    (for ([(α V) (in-hash Σᵥ)])
      (printf "* ~a ↦ ~a~n" (show-α α) (show-T V)))
    (when appendix?
      (printf "where:~n")
      (for ([α (in-hash-keys Σᵥ)])
        (printf "* ~a ≡ ~a~n" (show-α α) (inspect-α α)))))

  (: show-P : P → Sexp)
  (define show-P
    (match-lambda
      [(? -o? o) (show-o o)]
      [(P:≤ r) `(<=/c ,r)]
      [(P:< r) `(</c ,r)]
      [(P:> r) `(>/c ,r)]
      [(P:≥ r) `(>=/c ,r)]
      [(P:≡ b) (show-b b)]
      [(P:¬ P) `(not/c ,(show-P P))]
      [(P:arity-includes a) `(arity-includes/c ,(show-arity a))]))

  (define show-arity : (Arity → Sexp)
    (match-lambda
      [(? integer? n) n]
      [(arity-at-least k) `(arity-at-least ,k)]
      [(? list? l) (map show-arity l)]))

  (define show-Σ (show-map show-α show-T))
  (define show-Σₖ ((inst show-map αₖ (℘ Ξ:co) Sexp Index) show-αₖ (λ (Ξs) (set-count Ξs))))
  (define show-Ρ : (Ρ → (Listof (List Symbol '↦ Sexp))) ((inst show-map Symbol α Symbol Sexp) values show-α))
  )
