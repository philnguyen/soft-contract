#lang typed/racket/base

(provide pretty-print@)

(require typed/racket/unit
         racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         (only-in racket/list make-list)
         racket/string
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "signatures.rkt"
         )

(define-unit pretty-print@
  (import ast-pretty-print^ static-info^
          val^)
  (export pretty-print^)

  (define show-V : (V → Sexp)
    (match-lambda
      [(-b b) (show-b b)]
      [(-● Ps) (show-Ps Ps "●")]
      [(? -o? o) (show-o o)]
      [(? -λ? V) (show-e V)]
      [(? Clo? clo) (show-Clo clo)]
      [(Case-Clo clos ℓ) `(case-lambda ,@(map show-Clo clos))]
      [(Guarded _ G α) `(,(show-Prox/C G) ◃ ,(show-α α))]
      [(St (α:dyn (β:st-elems ctx 𝒾) _) Ps) `(,(-𝒾-name 𝒾) ,(show-ctx/ℓ ctx) ,(show-Ps Ps "_"))]
      [(Vect (α:dyn (β:vect-elems ℓ n) _)) (format-symbol "~a~a" (show-ℓ ℓ) (n-sup n))]
      [(Vect-Of α n) `(vector^ ,(show-α α) × ,(show-V^ n))]
      [(Empty-Hash) 'empty-hash]
      [(Hash-Of αₖ αᵥ) `(hash-of ,(show-α αₖ) ,(show-α αᵥ))]
      [(Empty-Set) '∅]
      [(Set-Of α) `(set-of ,(show-α α))]
      [(And/C α₁ α₂ ℓ) `(and/c ,(show-α α₁) ,(show-α α₂))]
      [(Or/C α₁ α₂ ℓ) `(or/c ,(show-α α₂) ,(show-α α₂))]
      [(Not/C α ℓ) `(not/c ,(show-α α))]
      [(X/C α) `(rec/c ,(show-α α))]
      [(One-Of/C bs) `(one-of/c ,@(set-map bs show-b))]
      [(? Prox/C? C) (show-Prox/C C)]
      [(Seal/C α _) `(seal/c ,(show-α α))]
      [(Sealed α) (format-symbol "sealed@~a" (assert (show-α α) symbol?))]
      [(? P? P) (show-P P)]
      [(? T? T) (show-T T)]))

  (define show-P : (P → Sexp)
    (match-lambda
      [(? -o? o) (show-o o)]
      [(P:> T) `(>/c ,(show-T T))]
      [(P:≥ T) `(≥/c ,(show-T T))]
      [(P:< T) `(</c ,(show-T T))]
      [(P:≤ T) `(≤/c ,(show-T T))]
      [(P:= T) `(=/c ,(show-T T))]
      [(P:≡ T) `(≡/c ,(show-T T))]
      [(P:arity-includes n) `(arity-includes/c ,(show-Arity n))]
      [(P:¬ Q) `(¬/c ,(show-P Q))]
      [(P:St acs P*) `(,(show-acs acs) ↝ ,(show-P P*))]
      [(P:vec-len n) `(vector-length/c ,n)]))

  (define (show-Ps [Ps : (℘ P)] [prefix : String]) : Symbol
    (string->symbol (string-join (set-map Ps (compose1 sexp->string show-P))
                                 "_" #:before-first prefix)))

  (define (show-acs [acs : (Listof -st-ac)])
    (string->symbol (string-join (map (compose1 symbol->string show-o) acs) ".")))

  (define show-Arity : (Arity → Sexp)
    (match-lambda
      [(? integer? n) n]
      [(arity-at-least n) `(arity-at-least ,n)]
      [(? list? as) (map show-Arity as)]))

  (define show-Clo : (Clo → Sexp)
    (match-lambda [(Clo xs _ _) `(λ ,(show-formals xs) …)]))

  (define show-Prox/C : (Prox/C → Sexp)
    (match-lambda
      [(? ==>i? V) (show-==>i V)]
      [(∀/C xs C _) `(∀/C ,xs …)]
      [(Case-=> cases) `(case-> ,@(map show-==>i cases))]
      [(? St/C? C) (define-values (_ ℓ 𝒾) (St/C-fields C))
                   (format-symbol "~a/c@~a" (-𝒾-name 𝒾) (show-ℓ ℓ))]
      [(Vectof/C α ℓ) `(vectorof ,(show-α α))]
      [(Vect/C α) `(vector/c ,(show-α α))]
      [(Hash/C αₖ αᵥ ℓ) `(hash/c ,(show-α αₖ) ,(show-α αᵥ))]
      [(Set/C α ℓ) `(set/c ,(show-α α))]))

  (define show-==>i : (==>i → Sexp)
    (match-lambda
      [(==>i (-var Dom:init ?Dom:rest) Rng)
       `(->i ,(map show-Dom Dom:init)
             ,@(if ?Dom:rest `(#:rest ,(show-Dom ?Dom:rest)) '())
             ,(match Rng
                [#f 'any]
                [(list d) (show-Dom d)]
                [(? values ds) `(values ,@(map show-Dom ds))]))]))

  (: show-V^ : V^ → Sexp)
  (define (show-V^ V^)
    (string->symbol (string-join (set-map V^ (compose1 sexp->string show-V))
                                 "|" #:before-first "{" #:after-last "}")))

  (: show-W : W → (Listof Sexp))
  (define (show-W W) (map show-V^ W))

  (define show-Dom : (Dom → (Listof Sexp))
    (match-lambda
      [(Dom x (Clo (-var xs #f) _ _) _) `(,x ,xs …)]
      [(Dom x (? α? α)               _)  `(,x ,(show-α α))]))

  (define show-T : ((U T -b) → Sexp)
    (match-lambda
      [(-b b) (show-b b)]
      [(T:@ o Ts) `(,(show-o o) ,@(map show-T Ts))]
      [(? α? α) (show-α α)]))

  (define show-α : (α → Sexp)
    (match-lambda
      [(α:dyn β H) (format-symbol "~a~a" (show-β β) (n-sup (intern-H H)))]
      [(γ:lex x) x]
      [(γ:top x) (-𝒾-name x)]
      [(γ:wrp x) (format-symbol "⟨~a⟩" (-𝒾-name x))]
      [(γ:hv hv-tag) (format-symbol "hv:~a" (show-HV-Tag hv-tag))]
      [(γ:imm V) (show-V V)]
      [(γ:imm:blob _ ℓ) (show-ℓ ℓ)]
      [(γ:imm:listof x V _) (format-symbol "~a:listof" x)]
      [(γ:escaped-field 𝒾 i) (format-symbol "escaped-~a" (show-o (-st-ac 𝒾 i)))]))

  (define show-β : (β → Symbol)
    (match-lambda
      [(β:clo ℓ) (show-ℓ ℓ)]
      [(β:mut x) (format-symbol "~a!" (if (symbol? x) x (-𝒾-name x)))]
      [(β:st-elems ctx 𝒾) (format-symbol "~a-~a" (-𝒾-name 𝒾) (show-ctx/ℓ ctx))]
      [(β:var:car tag idx) (format-symbol "var:car_~a_~a" tag (or idx '*))]
      [(β:var:cdr tag idx) (format-symbol "var:cdr_~a_~a" tag (or idx '*))]
      [(β:st 𝒾 _) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
      [(β:vect-elems ℓ n) (show-ℓ ℓ)]
      [(β:vct ℓ) (show-ℓ ℓ)]
      [(β:hash:key ℓ) (show-β:ℓ ℓ 0)]
      [(β:hash:val ℓ) (show-β:ℓ ℓ 1)]
      [(β:set:elem ℓ) (show-ℓ ℓ)]
      [(β:unvct ctx) (show-β:ctx ctx)]
      [(β:unhsh ctx _) (show-β:ctx ctx)]
      [(β:unset ctx _) (show-β:ctx ctx)]
      [(β:and/c:l ℓ) (show-β:ℓ ℓ 0)]
      [(β:and/c:r ℓ) (show-β:ℓ ℓ 1)]
      [(β:or/c:l ℓ) (show-β:ℓ ℓ 0)]
      [(β:or/c:r ℓ) (show-β:ℓ ℓ 1)]
      [(β:not/c ℓ) (show-ℓ ℓ)]
      [(β:x/c x) (format-symbol "rec-~a/c" x)]
      [(β:vect/c-elems ℓ n) (show-ℓ ℓ)]
      [(β:vectof ℓ) (show-ℓ ℓ)]
      [(β:hash/c:key _) 'hash/c:key]
      [(β:hash/c:val _) 'hash/c:val]
      [(β:set/c:elem _) 'set/c:elem]
      [(β:st/c-elems ℓ 𝒾) (show-ℓ ℓ)]
      [(β:dom ℓ) (show-ℓ ℓ)]
      [(β:fn ctx _) (show-β:ctx ctx)]
      [(β:sealed x _) (format-symbol "⦇~a⦈" x)]))

  (: show-β:ℓ (ℓ Natural → Symbol))
  (define (show-β:ℓ ℓ i) (format-symbol "~a@~a" (show-ℓ ℓ) i))

  (define show-β:ctx : (Ctx → Symbol)
    (match-lambda
      [(Ctx l+ l- ℓₒ ℓ)
       (format-symbol "~a-~a-~a"
                      (if (transparent-module? l+) '⊕ '⊖)
                      (show-ℓ ℓₒ)
                      (show-ℓ ℓ))]))

  (define show-HV-Tag : (HV-Tag → Symbol)
    (match-lambda
      [#f '•]
      [(? string? s) (string->symbol s)]
      [(? symbol? s) s]))

  (: show-Ξ : Ξ → (Listof Sexp))
  (define (show-Ξ Ξ)
    (for/list : (Listof Sexp) ([(α r) (in-hash Ξ)])
      (match-define (cons S n) r)
      (define ↦ (case n
                  [(0) '↦⁰]
                  [(1) '↦¹]
                  [(?) '↦?]
                  [(N) '↦ⁿ]))
      `(,(show-α α) ,↦ ,(show-S S))))

  (: show-Γ : Γ → Symbol)
  (define (show-Γ Γ)
    (string->symbol
     (string-join
      (for/list : (Listof String) ([(x Vs) (in-hash Γ)])
        (format "~a↦~a" (show-T x) (show-S Vs)))
      "∧"
      #:before-first "{"
      #:after-last "}")))

  (: show-Σ : Σ → (Listof Sexp))
  (define (show-Σ Σ)
    (match-define (cons Ξ Γ) Σ)
    `(,@(show-Ξ Ξ) ,(show-Γ Γ)))

  (: show-S : S → Sexp)
  (define (show-S S)
    (cond [(vector? S)
           (string->symbol
            (string-join
             (for/list : (Listof String) ([Vs (in-vector S)])
               (format "~a" (show-V^ Vs)))
             " "
             #:before-first "["
             #:after-last "]"))]
          [(hash? S) (show-Γ S)]
          [(set? S) (show-V^ S)]
          [else (show-α S)]))

  (: show-R : R → (Listof Sexp))
  (define (show-R r)
    (for/list : (Listof Sexp) ([(W ΔΣ) (in-hash r)])
      `(,(show-W W) @ ,@(set-map ΔΣ show-Σ))))

  (define show-Err : (Err → Sexp)
    (match-lambda
      [(Err:Raised s _) `(error ,s)]
      [(Err:Undefined x ℓ) `(undefined ,x ,(show-ℓ ℓ))]
      [(Err:Values n E W ℓ) `(wrong-number-of-values ,n ,@(show-W W) ,(show-ℓ ℓ))]
      [(Err:Arity f xs ℓ) `(wrong-number-of-arguments
                            ,(if (integer? f) (show-ℓ f) (show-V f))
                            ,(if (integer? xs) `(,xs args) (show-W xs))
                            ,(show-ℓ ℓ))]
      [(Err:Sealed x ℓ) `(inspect-sealed-value ,x ,(show-ℓ ℓ))]
      [(Blm l+ ℓ ℓₒ ctc val)
       `(blame ,l+ ,(show-ℓ ℓ) ,(show-ℓ ℓₒ) ,(show-W ctc) ,(show-W val))]))

  (define show-$:Key : ($:Key → Sexp)
    (match-lambda
      [($:Key:Exp Σ E)
       `(Exp ,(show-e E) @ ,@(show-Σ Σ))]
      [($:Key:Mon Σ Ctx V V^)
       `(Mon ,(show-V V) ,(show-V^ V^) @ ,@(show-Σ Σ))]
      [($:Key:Fc Σ ℓ V V^)
       `(Fc ,(show-V V) ,(show-V^ V^) @ ,@(show-Σ Σ))]
      [($:Key:App Σ ℓ V W)
       `(App ,(show-V V) ,@(show-W W) @ ,@(show-Σ Σ))]
      [($:Key:Hv Σ α)
       `(Hv ,(show-α α) @ ,@(show-Σ Σ))]))

  (define (sexp->string [s : Sexp]) (format "~a" s))
  
  (define intern-H : (H → Index)
    (let ([cache : (HashTable H Index) (make-hash)])
      (λ (H) (hash-ref! cache H (λ () (hash-count cache))))))

  (define show-ctx/ℓ : ((U Ctx ℓ (Pairof (U Symbol ℓ) (Option Index))) → Symbol)
    (match-lambda
      [(? integer? ℓ) (show-ℓ ℓ)]
      [(Ctx l+ _ ℓₒ ℓ)
       (format-symbol "~a-~a-~a" (if (transparent-module? l+) '⊕ '⊖) (show-ℓ ℓₒ) (show-ℓ ℓ))]
      [(cons x i)
       (format-symbol "~a@~a" (if (symbol? x) x (show-ℓ x)) (if i i 'N))]))
  )
