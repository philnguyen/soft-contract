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
  (import ast-pretty-print^)
  (export pretty-print^)

  (define show-V : (V → Sexp)
    (match-lambda
      [(-b b) (show-b b)]
      [(-● Ps) (string->symbol (string-join (set-map Ps (compose1 sexp->string show-P))
                                            "_" #:before-first "●"))]
      [(? -o? o) (show-o o)]
      [(? Clo? clo) (show-Clo clo)]
      [(Case-Clo clos ℓ) `(case-lambda ,@(map show-Clo clos))]
      [(Guarded _ G α) `(,(show-Prox/C G) ◃ …)]
      [(St 𝒾 αs) `(,(-𝒾-name 𝒾) ,@(make-list (length αs) '…))]
      [(Vect αs) `(vector ,@(make-list (length αs) '…))]
      [(Vect-Of α n) `(vector-of … × ,(show-V^ n))]
      [(Hash-Of αₖ αᵥ im?) `(,(if im? 'hash-of 'mutable-hash-of) …)]
      [(Set-Of α im?) `(,(if im? 'set-of 'mutable-set-of) ,(show-α α))]
      [(And/C _ _ ℓ) `(and/c … …)]
      [(Or/C _ _ ℓ) `(or/c … …)]
      [(Not/C _ ℓ) `(not/c …)]
      [(One-Of/C bs) `(one-of/c ,@(set-map bs show-b))]
      [(? Prox/C? C) (show-Prox/C C)]
      [(Seal/C α) `(seal/c ,(show-α α))]
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
      [(P:arity-includes n) `(arity-includes/c ,n)]
      [(P:¬ Q) `(¬/c ,(show-P Q))]))

  (define show-Clo : (Clo → Sexp)
    (match-lambda [(Clo xs _ _ _) `(λ ,(show-formals xs) …)]))

  (define show-Prox/C : (Prox/C → Sexp)
    (match-lambda
      [(? ==>? C) (show-==> C)]
      [(==>i Doms Rng) `(->i ,(map show-Dom Doms) ,(show-Dom Rng))]
      [(∀/C xs C Ρ) `(∀/C ,xs …)]
      [(Case-=> cases) `(case-> ,@(map show-==> cases))]
      [(St/C 𝒾 _ ℓ) `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) … ,(show-ℓ ℓ))]
      [(Vectof/C _ ℓ) `(vectorof … ,(show-ℓ ℓ))]
      [(Vect/C _ ℓ) `(vector/c … ,(show-ℓ ℓ))]
      [(Hash/C _ _ ℓ) `(hash/c … ,(show-ℓ ℓ))]
      [(Set/C _ ℓ) `(set/c … ,(show-ℓ ℓ))]))

  (define show-==> : (==> → Sexp)
    (match-lambda
      [(==> (-var _ ?x) ?y ℓ)
       (define rng (if ?y '… 'any))
       (if ?x `(… #:rest … . ->* . ,rng) `(… . -> . ,rng))]))

  (: show-V^ : V^ → Sexp)
  (define (show-V^ V^)
    (string->symbol (string-join (set-map V^ (compose1 sexp->string show-V))
                                 "," #:before-first "{" #:after-last "}")))

  (: show-W : W → Sexp)
  (define (show-W W) (map show-V^ W))

  (define show-Dom : (Dom → (Listof Sexp))
    (match-lambda
      [(Dom x (Clo (-var xs #f) _ _ _) _) `(,x ,xs …)]
      [(Dom x (? α? α)                _)  `(,x ,(show-α α))]))

  (define show-T : (T → Sexp)
    (match-lambda
      [(-b b) (show-b b)]
      [(T:@ o Ts) `(,(show-o o) ,@(map show-T Ts))]
      [(? α? α) (show-α α)]))

  (define show-α : (α → Sexp)
    (match-lambda
      [(α:dyn β H) (format-symbol "~a~a" (show-β β) (n-sub H))]
      [(γ:lex x) x]
      [(γ:top x) (-𝒾-name x)]
      [(γ:wrp x) (format-symbol "⟨~a⟩" (-𝒾-name x))]
      [(γ:hv hv-tag) (format-symbol "hv:~a" (show-HV-Tag hv-tag))]
      [(γ:imm V) (show-V V)]
      [(γ:imm:listof x V _) (format-symbol "~a:listof" x)]
      [(γ:imm:ref-listof x V _) (format-symbol "~a:ref-listof" x)]))

  (define show-β : (β → Symbol)
    (match-lambda
      [(? symbol? x) x]
      [(β:mut x) (format-symbol "~a!" (if (symbol? x) x (-𝒾-name x)))]
      [(β:fld 𝒾 _ i) (format-symbol "~a@~a" (-𝒾-name 𝒾) i)]
      [(β:var:car tag idx) (format-symbol "var:car_~a_~a" tag (or idx '*))]
      [(β:var:cdr tag idx) (format-symbol "var:cdr_~a_~a" tag (or idx '*))]
      [(β:st 𝒾 _) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
      [(β:idx _ i) (format-symbol "@~a" i)]
      [(β:vct _) '@*]
      [(β:hash:key _) 'hash:key]
      [(β:hash:val _) 'hash:val]
      [(β:set:elem _) 'set:elem]
      [(β:unvct _) 'inner-vect]
      [(β:unhsh _) 'inner-hash]
      [(β:unset _) 'inner-set]
      [(β:and/c:l _) 'and/c:l]
      [(β:and/c:r _) 'and/c:r]
      [(β:or/c:l _) 'or/c:l]
      [(β:or/c:r _) 'or/c:r]
      [(β:not/c _) 'not/c]
      [(β:x/c x) (format-symbol "rec-~a/c" x)]
      [(β:vect/c _ i) (format-symbol "vect/c@~a" i)]
      [(β:vectof _) 'vectof]
      [(β:hash/c:key _) 'hash/c:key]
      [(β:hash/c:val _) 'hash/c:val]
      [(β:set/c:elem _) 'set/c:elem]
      [(β:st/c 𝒾 _ i) (format-symbol "~a@~a" (-𝒾-name 𝒾) i)]
      [(β:dom _ i) (format-symbol "dom@~a" i)]
      [(β:rst _) 'dom@rst]
      [(β:rng _ _ i) (format-symbol "rng@~a" i)]
      [(β:fn _) 'inner-fun]
      [(β:sealed x) (format-symbol "⦇~a⦈" x)]))

  (define show-HV-Tag : (HV-Tag → Symbol)
    (match-lambda
      [#f '•]
      [(? string? s) (string->symbol s)]
      [(? symbol? s) s]))

  (: show-Σ : Σ → (Listof Sexp))
  (define (show-Σ Σ)
    (for/list : (Listof Sexp) ([(T r) (in-hash Σ)])
      (match-define (cons Vs n) r)
      (define ↦ (case n
                  [(0) '↦⁰]
                  [(1) '↦¹]
                  [(N) '↦ⁿ]))
      `(,(show-T T) ,↦ ,(show-V^ Vs))))

  (define (sexp->string [s : Sexp]) (format "~a" s))
  )
