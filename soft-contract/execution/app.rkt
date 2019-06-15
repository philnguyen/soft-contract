#lang typed/racket/base

(provide app@)

(require racket/set
         racket/list
         racket/match
         racket/vector
         (only-in racket/function curry)
         typed/racket/unit
         syntax/parse/define
         set-extras
         bnf
         unreachable
         "../utils/map.rkt"
         "../utils/patterns.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt"
         )

(⟦F⟧ . ≜ . (Σ ℓ W → R))
(⟦G⟧ . ≜ . (Σ ℓ W V^ → R))

(define-unit app@
  (import meta-functions^ static-info^
          sto^ cache^ val^ pretty-print^
          prims^ prover^
          exec^ evl^ mon^ hv^ gc^ termination^)
  (export app^)

  ;; A call history tracks the call chain that leads to the current expression, modulo loops
  (Stk . ≜ . (Listof E))
  (define current-chain ((inst make-parameter Stk) '()))
  ;; Global table remembering the widest store for each chain
  ;; FIXME: memory leak. Reset for each program.
  (define global-stores : (HashTable (Pairof Stk Γ) Σ) (make-hash))

  (: app : Σ ℓ V^ W → R)
  (define (app Σ ℓ Vₕ^ W*)
    (define-values (W ΔΣ₁) (escape-clos Σ W*))
    (define W:root (W-root W))
    (define r
      ((inst fold-ans V)
       (λ (Vₕ)
         (define root (∪ W:root (V-root Vₕ)))
         (define Σ* (gc root (⧺ Σ ΔΣ₁)))
         (ref-$! ($:Key:App Σ* (current-MS) ℓ Vₕ W)
                 (λ () (gc-R root Σ* (ΔΣ⧺R ΔΣ₁ (app₁ Σ* ℓ Vₕ W))))))
       (unpack Vₕ^ Σ)))

    (define Tₐ : (Option T)
      (match* (Vₕ^ W*)
        [({singleton-set (? K? o)}
          (list {singleton-set (and #{Tₓ : (Listof (U T -b))} (or (? -b?) (? T?)))} ...))
         #:when (for/or : Boolean ([T (in-list Tₓ)])
                  (or (γ? T)
                      (and (T:@? T) (not (set-empty? (T-root T))))))
         (T:@/simp o Tₓ)]
        [(_ _) #f]))
    (if Tₐ
        (let ([Wₐ* (list {set Tₐ})])
          (for/fold ([r* : R r])
                    ([(Wₐ ΔΣs) (in-hash r)]
                     #:when (= 1 (length Wₐ)))
            (match-define (list Vsₐ) Wₐ)
            (for/fold ([r* : R (hash-remove r* Wₐ)])
                      ([ΔΣᵢ : ΔΣ (in-set ΔΣs)])
              (define Vsₐ* (unpack Vsₐ (⧺ Σ ΔΣᵢ)))
              (define ΔΣ*
                (match Tₐ ; ignore mapping for symbolic accesses
                  [(T:@ (? -st-ac?) _) ΔΣᵢ]
                  [_
                   (match-define (cons ΔΞ ΔΓ) ΔΣᵢ)
                   (define Vsₐ**
                     (match (hash-ref ΔΓ Tₐ #f)
                       [(? set? Vsₐ₀) (V⊓ Vsₐ₀ Vsₐ*)]
                       [#f Vsₐ*]))
                   (and Vsₐ**
                        (let ([ΔΓ₁ (hash-set ΔΓ Tₐ Vsₐ**)])
                          (define ΔΓ*
                            (match Vsₐ
                              [{singleton-set (? T? T*)}
                               (hash-set ΔΓ₁ (T:@ (K:≡) (list Tₐ T*)) {set -tt})]
                              [_ ΔΓ₁]))
                          (cons ΔΞ ΔΓ*)))]))
              (if ΔΣ*
                  (hash-update r* Wₐ* (λ ([ΔΣs* : (℘ ΔΣ)]) (set-add ΔΣs* ΔΣ*)) mk-∅)
                  r*))))
        r))

  (: app/C : Σ ℓ V^ W → R)
  (define (app/C Σ ℓ Cs W)
    (define-values (bs Cs*) (set-partition -b? Cs))
    (R⊔ (cond [(set-empty? Cs*) ⊥R]
              [else (app Σ ℓ Cs* W)])
        (cond [(set-empty? bs) ⊥R]
              [else (app₁ Σ ℓ 'equal? (cons bs W))])))

  (: app₁ : Σ ℓ V W → R)
  (define (app₁ Σ ℓ V W)
    (define f (match V
                [(? -λ? V) (app-λ V)]
                [(? Clo? V) (app-Clo V)]
                [(? Case-Clo? V) (app-Case-Clo V)]
                [(-st-mk 𝒾) (app-st-mk 𝒾)]
                [(-st-p 𝒾) (app-st-p 𝒾)]
                [(-st-ac 𝒾 i) (app-st-ac 𝒾 i)]
                [(-st-mut 𝒾 i) (app-st-mut 𝒾 i)]
                [(? symbol? o) (app-prim o)]
                [(Guarded ctx (? Fn/C? G) α)
                 (cond [(==>i? G) (app-==>i ctx G α)]
                       [(∀/C? G) (app-∀/C  ctx G α)]
                       [else     (app-Case-=> ctx G α)])]
                [(And/C α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-And/C α₁ α₂ ℓ)]
                [(Or/C  α₁ α₂ ℓ) #:when (C-flat? V Σ) (app-Or/C  α₁ α₂ ℓ)]
                [(Not/C α ℓ) (app-Not/C α ℓ)]
                [(X/C α) (app-X/C α)]
                [(One-Of/C bs) (app-One-Of/C bs)]
                [(? St/C?) #:when (C-flat? V Σ) (app-St/C V)]
                [(-● Ps) (app-opq Ps)]
                [(P:≡ T) (app-P 'equal? T)]
                [(P:= T) (app-P '= T)]
                [(P:> T) (app-P '< T)]
                [(P:≥ T) (app-P '<= T)]
                [(P:< T) (app-P '> T)]
                [(P:≤ T) (app-P '>= T)]
                [V (app-err! V)]))
    (f Σ ℓ W))

  (: app-λ : -λ → ⟦F⟧)
  (define ((app-λ Vₕ) Σ ℓ Wₓ*)
    (match-define (-λ fml E ℓₕ) Vₕ)
    (with-guarded-arity Wₓ* ℓₕ ℓ
      [(app length (? (curry arity-includes? (shape fml))))
       (with-sct-guard Σ ℓ Vₕ Wₓ*
         (λ ()
           (define-values (ΔΣₓ Wₓ) (alloc-args Σ fml Wₓ*))
           ;; gc one more time against unpacked arguments
           ;; TODO: clean this up so only need to gc once?
           ;; TODO: code dup
           (let* ([root (∪ (E-root Vₕ) (W-root Wₓ))]
                  [Σ₁ (gc root Σ)])
             (define rₐ (evl/history (⧺ Σ₁ ΔΣₓ) E))
             (define rn (make-renamings fml Wₓ*))
             (fix-return rn Σ₁ (R-escape-clos Σ₁ (ΔΣ⧺R ΔΣₓ rₐ))))))]))

  (: app-Clo : Clo → ⟦F⟧)
  (define ((app-Clo Vₕ) Σ ℓ Wₓ*)
    (match-define (Clo fml E (and αₕ (α:dyn (β:clo ℓₕ) _))) Vₕ)
    (with-guarded-arity Wₓ* ℓₕ ℓ
      [(app length (? (curry arity-includes? (shape fml))))
       (with-sct-guard Σ ℓ (-λ fml E ℓₕ) Wₓ*
         (λ ()
           (define-values (ΔΣₓ Wₓ) (alloc-args Σ fml Wₓ*))
           ;; gc one more time against unpacked arguments
           ;; TODO: clean this up so only need to gc once?
           (let* ([root (∪ (V-root Vₕ) (W-root Wₓ))]
                  [Γ* (Σ@/env αₕ Σ)]
                  [Σ₁ (cons (car (gc root Σ)) Γ*)])
             (define rₐ (evl/history (⧺ Σ₁ ΔΣₓ) E)) ; no `ΔΣₓ` in result
             (define rn (insert-fv-erasures Γ* (make-renamings fml Wₓ*)))
             (fix-return rn Σ₁ (R-escape-clos Σ₁ (ΔΣ⧺R ΔΣₓ rₐ))))))]))

  (: alloc-args : Σ -formals W → (Values ΔΣ W))
  ;; Unpack and allocate the arguments given parameter list
  (define (alloc-args Σ fml W*)
    (define W (unpack-W W* Σ))
    (match-define (-var xs xᵣ) fml)
    (define-values (W₀ Wᵣ) (if xᵣ (split-at W (length xs)) (values W '())))
    (values (⧺ (alloc-lex* Σ xs W₀)
               (if xᵣ (alloc-vararg Σ xᵣ Wᵣ) ⊥ΔΣ)
               (cons ⊥Ξ (rename-props Σ xs W*)))
            W))

  (: rename-props : Σ (Listof Symbol) W → Γ)
  (define (rename-props Σ xs W)
    (define caller-props
      (for/hash : Γ ([(T D) (in-hash (cdr Σ))] #:when (prop? T D))
        (values T D)))

    (: acc-rn : Renamings γ T → Renamings)
    (define (acc-rn rn lhs rhs)
      (let loop ([rn : Renamings rn] [lhs : T lhs] [rhs : T rhs])
        (define rn* (hash-set rn rhs lhs))
        (match rhs
          [(T:@ (-st-mk 𝒾) Ts)
           (for/fold ([rn : Renamings rn*])
                     ([(Tᵢ i) (in-indexed Ts)] #:when (T? Tᵢ))
             (loop rn (T:@ (-st-ac 𝒾 (assert i index?)) (list lhs)) Tᵢ))]
          [_ rn*])))
    (define rn
      (rename (for/fold ([rn : Renamings (hash)])
                        ([x (in-list xs)]
                         [Vs (in-list W)]
                         #:when (= 1 (set-count Vs))
                         [V (in-value (set-first Vs))]
                         #:when (T? V))
                (acc-rn rn (γ:lex x) V))))
    (for*/hash : Γ ([(T D) (in-hash caller-props)]
                    [T* (in-value (rn T))] #:when (T? T*))
      (values T* D)))

  (: with-sct-guard : Σ ℓ V W (→ R) → R)
  (define (with-sct-guard Σ ℓ ee:raw W comp)
    (define ee (check-point ee:raw))
    (match (current-MS)
      [(MS l+ ℓₒ M)
       (match (current-app)
         [(? values er)
          (match (update-M Σ M er ee W)
            [(? values M*)
             (parameterize ([current-MS (MS l+ ℓₒ M*)]
                            [current-app ee])
               (comp))]
            [#f (err! (Err:Term l+ ℓ ℓₒ (assert ee -λ?) W))
                ⊥R])]
         [#f (parameterize ([current-app ee])
               (comp))])]
      [#f (comp)]))

  (: evl/history : Σ E → R)
  (define (evl/history Σ₁ E)
    (define stk (current-chain))
    (define stk* (cond [(memq E stk) => values]
                       [else (cons E stk)]))
    (define k (cons stk* (remove-props (cdr Σ₁))))
    (define Σ* (match (hash-ref global-stores k #f)
                 [(? values Σ₀) (ΔΣ⊔ Σ₀ Σ₁)]
                 [_ Σ₁]))
    (hash-set! global-stores k Σ*)
    (parameterize ([current-chain stk*])
      (evl Σ* E)))

  (: remove-props : Γ → Γ)
  (define (remove-props Γ₀)
    (for/fold ([acc : Γ Γ₀]) ([(T D) (in-hash Γ₀)] #:when (prop? T D))
      (hash-remove acc T)))

  (: app-Case-Clo : Case-Clo → ⟦F⟧)
  (define ((app-Case-Clo Vₕ) Σ ℓ Wₓ)
    (match-define (Case-Clo cases ℓₕ) Vₕ)
    (define n (length Wₓ))
    (match ((inst findf Clo) (λ (clo) (arity-includes? (shape (Clo-_0 clo)) n)) cases)
      [(? values clo) ((app-Clo clo) Σ ℓ Wₓ)]
      [#f (err! (Err:Arity ℓₕ n ℓ)) ⊥R]))

  (: app-st-mk : -𝒾 → ⟦F⟧)
  (define ((app-st-mk 𝒾) Σ ℓ Wₓ)
    (define n (count-struct-fields 𝒾))
    (if (= n (length Wₓ))
        (let ([α (α:dyn (β:st-elems ℓ 𝒾) H₀)])
          (R-of (St α ∅) (alloc α (list->vector (unpack-W Wₓ Σ)))))
        (begin (err! (Err:Arity (-st-mk 𝒾) (length Wₓ) ℓ))
               ⊥R)))

  (: app-st-p : -𝒾 → ⟦F⟧)
  (define ((app-st-p 𝒾) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-p 𝒾) ℓ
      [(list _) (implement-predicate Σ (-st-p 𝒾) Wₓ)]))

  (: app-st-ac : -𝒾 Index → ⟦F⟧)
  (define ((app-st-ac 𝒾 i) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-ac 𝒾 i) ℓ
      [(list Vₓ)
       (with-split-Σ Σ (-st-p 𝒾) Wₓ
         (λ (Wₓ* ΔΣ₁) (ΔΣ⧺R ΔΣ₁ ((unchecked-app-st-ac 𝒾 i) (⧺ Σ ΔΣ₁) ℓ (car Wₓ*))))
         (λ (Wₓ* ΔΣ₂)
           (define ℓₒ (ℓ-with-src +ℓ₀ (-𝒾-name 𝒾)))
           (err! (blm (ℓ-src ℓ) ℓ ℓₒ (list {set (-st-p 𝒾)}) Wₓ*))
           ⊥R))]))

  (: unchecked-app-st-ac : -𝒾 Index → Σ ℓ V^ → R)
  (define ((unchecked-app-st-ac 𝒾 i) Σ ℓ Vₓ)
    (define ac₁ : (V → R)
      (match-lambda
        [(St α Ps)
         (define Vᵢ (vector-ref (Σ@/blob α Σ) i))
         (define-values (V* ΔΣ)
           (refine (unpack Vᵢ Σ) (ac-Ps (-st-ac 𝒾 i) Ps) Σ))
         (R-of V* ΔΣ)]
        [(Guarded (cons l+ l-) (? St/C? C) αᵥ)
         (define-values (αₕ ℓₕ _) (St/C-fields C))
         (define Cᵢ (vector-ref (Σ@/blob αₕ Σ) i))
         (with-collapsing/R [(ΔΣ Ws) ((unchecked-app-st-ac 𝒾 i) Σ ℓ (Σ@ αᵥ Σ))]
           (ΔΣ⧺R ΔΣ (mon (⧺ Σ ΔΣ) (Ctx l+ l- ℓₕ ℓ) Cᵢ (car (collapse-W^ Ws)))))]
        [(and V₀ (-● Ps))
         (case (sat Σ (-st-p 𝒾) {set V₀})
           [(✗) ⊥R]
           [else (R-of (st-ac-● 𝒾 i Ps Σ))])]
        [_ ⊥R]))
    
    (fold-ans/collapsing ac₁ (unpack Vₓ Σ)))

  (: st-ac-● : -𝒾 Index (℘ P) Σ → V^)
  (define (st-ac-● 𝒾 i Ps Σ)
    (define V
      (if (prim-struct? 𝒾)
          {set (-● ∅)}
          ;; Track access to user-defined structs
          (Σ@ (γ:escaped-field 𝒾 i) Σ)))
    (define-values (V* _) (refine V (ac-Ps (-st-ac 𝒾 i) Ps) Σ))
    V*)

  (: app-st-mut : -𝒾 Index → ⟦F⟧)
  (define ((app-st-mut 𝒾 i) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (-st-mut 𝒾 i) ℓ
      [(list Vₓ V*)
       (with-split-Σ Σ (-st-p 𝒾) (list Vₓ)
         (λ (Wₓ* ΔΣ₁) (ΔΣ⧺R ΔΣ₁ ((unchecked-app-st-mut 𝒾 i) (⧺ Σ ΔΣ₁) ℓ (car Wₓ*) V*)))
         (λ (Wₓ* ΔΣ₂) (err! (blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set (-st-p 𝒾)}) Wₓ*))
            ⊥R))]))

  (: unchecked-app-st-mut : -𝒾 Index → Σ ℓ V^ V^ → R)
  (define ((unchecked-app-st-mut 𝒾 i) Σ ℓ Vₓ V*₀)
    (define V* (unpack V*₀ Σ))
    ((inst fold-ans V)
     (match-lambda
       [(St α _)
        (define S (Σ@/blob α Σ))
        (define S* (vector-copy S))
        (vector-set! S* i V*)
        (R-of -void (mut α S* Σ))]
       [(Guarded (cons l+ l-) (? St/C? C) αᵥ)
        (define-values (αₕ ℓₕ _) (St/C-fields C))
        (define Cᵢ (vector-ref (Σ@/blob αₕ Σ) i))
        (with-collapsing/R [(ΔΣ Ws) (mon Σ (Ctx l- l+ ℓₕ ℓ) Cᵢ V*)]
          (ΔΣ⧺R ΔΣ ((unchecked-app-st-mut 𝒾 i) (⧺ Σ ΔΣ) ℓ (Σ@ αᵥ Σ) V*)))]
       [(? -●?) (R-of -void (alloc (γ:hv #f) V*))]
       [_ ⊥R])
     (unpack Vₓ Σ)))

  (: app-prim : Symbol → ⟦F⟧)
  (define ((app-prim o) Σ ℓ Wₓ)
    ; TODO massage raw result
    ((get-prim o) Σ ℓ Wₓ))

  (: app-==>i : (Pairof -l -l) ==>i α → ⟦F⟧)
  (define ((app-==>i ctx:saved G αₕ) Σ₀-full ℓ Wₓ*)
    (match-define (cons l+ l-) ctx:saved)
    (define Wₓ (unpack-W Wₓ* Σ₀-full))
    (define Σ₀ (gc (∪ (set-add (V-root G) αₕ) (W-root Wₓ)) Σ₀-full))
    (match-define (==>i (-var Doms ?Doms:rest) Rngs ?total) G)

    (: mon-doms : Σ -l -l (Listof Dom) W → R)
    (define (mon-doms Σ₀ l+ l- Doms₀ Wₓ₀)
      (let go ([Σ : Σ Σ₀] [Doms : (Listof Dom) Doms₀] [Wₓ : W Wₓ₀])
        (match* (Doms Wₓ)
          [('() '()) (R-of '())]
          [((cons Dom Doms) (cons Vₓ Wₓ))
           (with-each-path ([(ΔΣₓ Wₓ*) (mon-dom Σ l+ l- Dom Vₓ)]
                            [(ΔΣ* W*) (go (⧺ Σ ΔΣₓ) Doms Wₓ)])
             (R-of (cons (car Wₓ*) W*) (⧺ ΔΣₓ ΔΣ*)))]
          [(_ _)
           (define Cs
             (for/list : W ([D (in-list Doms₀)])
               (match (Dom-ctc D)
                 [(? Clo? C) {set C}]
                 [(? α? α) (unpack (Σ@ α Σ₀) Σ₀)])))
           (err! (blm l+ ℓ #|FIXME|# (ℓ-with-src +ℓ₀ 'Λ) Cs Wₓ₀))
           ⊥R])))

    (: mon-dom : Σ -l -l Dom V^ → R)
    (define (mon-dom Σ l+ l- dom V)
      (match-define (Dom x c ℓₓ) dom)
      (define ctx (Ctx l+ l- ℓₓ ℓ))
      (match c
        ;; Dependent domain
        [(Clo (-var xs #f) E (and αₕ (α:dyn (β:clo ℓ) _)))
         (define Σ₀
           (match-let ([(cons Ξ Γ:ctx) Σ])
             (define Γ* ; TODO make sure ok due to "closure" in `->i` not being general
               (for/fold ([Γ* : Γ Γ:ctx])
                         ([(T D) (in-hash (Σ@/env αₕ Σ))]
                          #:unless (hash-has-key? Γ* T))
                 (hash-set Γ* T D)))
             (cons Ξ Γ*)))
         (with-each-path ([(ΔΣ₁ W) (evl Σ₀ E)]
                         [(ΔΣ₂ W) (mon (⧺ Σ₀ ΔΣ₁) ctx (car W) V)])
           (match-define (list V*) W) ; FIXME catch
           (R-of W (⧺ ΔΣ₁ ΔΣ₂ (alloc-lex Σ x V*))))]
        ;; Non-dependent domain
        [(? α? α)
         (with-each-path ([(ΔΣ W) (mon Σ ctx (Σ@ α Σ₀) V)])
           (match-define (list V*) W)
           (R-of W (⧺ ΔΣ (alloc-lex Σ x V*))))]))

    (define Dom-ref (match-lambda [(Dom x _ _) {set (γ:lex x)}]))

    ;; Maybe monitor the result from applying the inner function
    (define (with-result [ΔΣ-acc : ΔΣ] [comp : (→ R)])
      (define r
        (if Rngs
            (with-each-path ([(ΔΣₐ Wₐ) (comp)])
              (ΔΣ⧺R (⧺ ΔΣ-acc ΔΣₐ) (mon-doms (⧺ Σ₀ ΔΣ-acc ΔΣₐ) l+ l- Rngs Wₐ)))
            (ΔΣ⧺R ΔΣ-acc (comp))))
      (fix-return (make-renamings (map Dom-name Doms) Wₓ*) Σ₀ r))

    (: maybe-check-termination : (→ R) → (→ R))
    (define ((maybe-check-termination comp))
      (with-sct-guard Σ₀ ℓ (Guarded ctx:saved G αₕ) Wₓ*
        (cond [(not ?total) comp]
              [else (λ ()
                      (parameterize ([current-MS
                                      (MS l+ ?total (match (current-MS)
                                                      [(MS _ _ M) M]
                                                      [#f         (hash)]))])
                        (comp)))])))

    (with-guarded-arity Wₓ G ℓ
      [Wₓ
       #:when (and (not ?Doms:rest) (= (length Wₓ) (length Doms)))
       (with-each-path ([(ΔΣₓ _) (mon-doms Σ₀ l- l+ Doms Wₓ)])
         (define args (map Dom-ref Doms))
         (with-result ΔΣₓ (maybe-check-termination (λ () (app (⧺ Σ₀ ΔΣₓ) ℓ (Σ@ αₕ Σ₀) args)))))]
      [Wₓ
       #:when (and ?Doms:rest (>= (length Wₓ) (length Doms)))
       (define-values (W₀ Wᵣ) (split-at Wₓ (length Doms)))
       (define-values (Vᵣ ΔΣᵣ) (alloc-rest (Dom-loc ?Doms:rest) Wᵣ))
       (with-each-path ([(ΔΣ-init _) (mon-doms Σ₀ l- l+ Doms W₀)]
                       [(ΔΣ-rest _) (mon-dom (⧺ Σ₀ ΔΣ-init ΔΣᵣ) l- l+ ?Doms:rest Vᵣ)])
         (define args-init (map Dom-ref Doms))
         (define arg-rest (Dom-ref ?Doms:rest))
         (with-result (⧺ ΔΣ-init ΔΣᵣ ΔΣ-rest)
           (maybe-check-termination
            (λ () (app/rest (⧺ Σ₀ ΔΣ-init ΔΣᵣ ΔΣ-rest) ℓ (Σ@ αₕ Σ₀) args-init arg-rest)))))]))

  (: app-∀/C : (Pairof -l -l) ∀/C α → ⟦F⟧)
  (define ((app-∀/C ctx G α) Σ₀ ℓ Wₓ)
    (with-each-path ([(ΔΣ Wₕ) (inst-∀/C Σ₀ ctx G α ℓ)])
      (ΔΣ⧺R ΔΣ (app (⧺ Σ₀ ΔΣ) ℓ (car Wₕ) Wₓ))))

  (: app-Case-=> : (Pairof -l -l) Case-=> α → ⟦F⟧)
  (define ((app-Case-=> ctx G α) Σ ℓ Wₓ)
    (define n (length Wₓ))
    (match-define (Case-=> Cs) G)
    (match ((inst findf ==>i)
            (match-lambda [(==>i doms _ _) (arity-includes? (shape doms) n)])
            Cs)
      [(? values C) ((app-==>i ctx C α) Σ ℓ Wₓ)]
      [#f (err! (Err:Arity G n ℓ)) ⊥R]))

  (: app-And/C : α α ℓ → ⟦F⟧)
  (define ((app-And/C α₁ α₂ ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-path ([(ΔΣ₁ W₁) (app/C Σ ℓ (Σ@ α₁ Σ) Wₓ)])
         (define Σ₁ (⧺ Σ ΔΣ₁))
         (with-split-Σ Σ₁ 'values W₁
           (λ (_ ΔΣ*) (ΔΣ⧺R (⧺ ΔΣ₁ ΔΣ*) (app/C (⧺ Σ₁ ΔΣ*) ℓ (Σ@ α₂ Σ) Wₓ)))
           (λ (_ ΔΣ*) (R-of -ff (⧺ ΔΣ₁ ΔΣ*)))))]))

  (: app-Or/C : α α ℓ → ⟦F⟧)
  (define ((app-Or/C α₁ α₂ ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-path ([(ΔΣ₁ W₁) (app/C Σ ℓ (Σ@ α₁ Σ) Wₓ)])
         (define Σ₁ (⧺ Σ ΔΣ₁))
         (with-split-Σ Σ₁ 'values W₁
           (λ (_ ΔΣ*) (R-of W₁ (⧺ ΔΣ₁ ΔΣ*)))
           (λ (_ ΔΣ*) (ΔΣ⧺R (⧺ ΔΣ₁ ΔΣ*) (app/C (⧺ Σ₁ ΔΣ*) ℓ (Σ@ α₂ Σ) Wₓ)))))]))

  (: app-Not/C : α ℓ → ⟦F⟧)
  (define ((app-Not/C α ℓₕ) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list _)
       (with-each-path ([(ΔΣ W) (app/C Σ ℓ (Σ@ α Σ) Wₓ)])
         (define Σ* (⧺ Σ ΔΣ))
         (with-split-Σ Σ* 'values W
           (λ (_ ΔΣ*) (R-of -ff (⧺ ΔΣ ΔΣ*)))
           (λ (_ ΔΣ*) (R-of -tt (⧺ ΔΣ ΔΣ*)))))]))

  (: app-X/C : α → ⟦F⟧)
  (define ((app-X/C α) Σ ℓ Wₓ) (app/C Σ ℓ (Σ@ α Σ) (unpack-W Wₓ Σ)))

  (: app-One-Of/C : (℘ Base) → ⟦F⟧)
  (define ((app-One-Of/C bs) Σ ℓ Wₓ)
    (with-guarded-arity Wₓ (One-Of/C bs) ℓ
      [(list V)
       (with-split-Σ Σ (One-Of/C bs) Wₓ
         (λ (_ ΔΣ) (R-of -tt ΔΣ))
         (λ (_ ΔΣ) (R-of -ff ΔΣ)))]))

  (: app-St/C : St/C → ⟦F⟧)
  (define ((app-St/C C) Σ ℓ Wₓ)
    (define-values (α ℓₕ 𝒾) (St/C-fields C))
    (define S (Σ@/blob α Σ))
    (with-guarded-arity Wₓ ℓₕ ℓ
      [(list Vₓ)
       (with-split-Σ Σ (-st-p 𝒾) Wₓ
         (λ (Wₓ* ΔΣ*) (ΔΣ⧺R ΔΣ* ((app-St/C-fields 𝒾 0 S ℓₕ) (⧺ Σ ΔΣ*) ℓ (car Wₓ*))))
         (λ (_ ΔΣ*) (R-of -ff ΔΣ*)))]))

  (: app-St/C-fields : -𝒾 Index (Vectorof V^) ℓ → Σ ℓ V^ → R)
  (define ((app-St/C-fields 𝒾 i Cs ℓₕ) Σ₀ ℓ Vₓ)
    (let loop ([i : Index 0] [Σ : Σ Σ₀])
      (if (>= i (vector-length Cs))
          (R-of -tt)
          (with-collapsing/R [(ΔΣᵢ Wᵢs) ((unchecked-app-st-ac 𝒾 i) Σ ℓ Vₓ)]
            (with-each-path ([(ΔΣₜ Wₜ) (app/C (⧺ Σ ΔΣᵢ) ℓ (vector-ref Cs i) (collapse-W^ Wᵢs))])
              (define ΔΣ (⧺ ΔΣᵢ ΔΣₜ))
              (define Σ* (⧺ Σ ΔΣ))
              (with-split-Σ Σ* 'values Wₜ
                (λ _ (ΔΣ⧺R ΔΣ (loop (assert (+ 1 i) index?) Σ*)))
                (λ _ (R-of -ff ΔΣ))))))))

  (: app-opq : (℘ P) → ⟦F⟧)
  (define ((app-opq Ps) Σ ℓ Wₓ*)
    (define Wₕ (list {set (-● Ps)}))
    (define ℓₒ (ℓ-with-src +ℓ₀ 'Λ))
    (with-split-Σ Σ 'procedure? Wₕ
      (λ _
        (define P-arity (P:arity-includes (length Wₓ*)))
        (with-split-Σ Σ P-arity Wₕ
          (λ _
            (define (run-opq)
              (leak Σ (γ:hv #f) ((inst foldl V^ V^) ∪ ∅ (unpack-W Wₓ* Σ))))
            (cond
              [(not (transparent-module? (ℓ-src ℓ))) (run-opq)]
              [(current-MS) => (match-lambda
                                 [(MS l+ ℓₒ _)
                                  (err! (Err:Term l+ ℓ ℓₒ (-● Ps) Wₓ*))
                                  (run-opq)])]
              [else (run-opq)]))
          (λ _ (err! (blm (ℓ-src ℓ) ℓ ℓₒ (list {set P-arity}) Wₕ))
             ⊥R)))
      (λ _ (err! (blm (ℓ-src ℓ) ℓ ℓₒ (list {set 'procedure?}) Wₕ))
         ⊥R)))

  (: app-P : Symbol (U T -b) → ⟦F⟧)
  (define ((app-P o T) Σ ℓ Wₓ) ((app-prim o) Σ ℓ (cons {set T} Wₓ)))

  (: app-err! : V → ⟦F⟧)
  (define ((app-err! V) Σ ℓ Wₓ)
    (err! (blm (ℓ-src ℓ) ℓ +ℓ₀ (list {set 'procedure?}) (list {set V})))
    ⊥R)

  (: app/rest : Σ ℓ V^ W V^ → R)
  (define (app/rest Σ ℓ Vₕ^ Wₓ Vᵣ)
    (define args:root (∪ (W-root Wₓ) (V^-root Vᵣ)))
    (define-values (Wᵣs snd?) (unalloc Vᵣ Σ))
    (unless snd?
      (err! (Err:Varargs Wₓ Vᵣ ℓ)))
    (fold-ans (λ ([Wᵣ : W]) (app Σ ℓ Vₕ^ (append Wₓ Wᵣ))) Wᵣs))

  (: insert-fv-erasures : Γ Renamings → Renamings)
  ;; Add erasure of free variables that were stack-copied
  (define (insert-fv-erasures Γ rn)
    (for/fold ([rn : Renamings rn]) ([γ (in-hash-keys Γ)]
                                     #:when (γ:lex? γ)
                                     #:unless (hash-has-key? rn γ))
      (hash-set rn γ #f)))

  (: unalloc : V^ Σ → (Values (℘ W) Boolean))
  ;; Convert list in object language into one in meta-language
  (define (unalloc Vs Σ)
    (define-set touched : α #:mutable? #t)
    (define elems : (Mutable-HashTable Integer V^) (make-hasheq))
    (define-set ends : Integer #:eq? #t #:mutable? #t)
    (define sound? : Boolean #t)

    (let touch! ([i : Integer 0] [Vs : V^ Vs])
      (for ([V (in-set Vs)])
        (match V
          [(St (and α (α:dyn (β:st-elems _ (== -𝒾-cons)) _)) _)
           (match-define (vector Vₕ Vₜ) (Σ@/blob α Σ))
           (hash-update! elems i (λ ([V₀ : V^]) (V⊔ V₀ Vₕ)) mk-∅)
           (cond [(touched-has? α)
                  (set! sound? #f)
                  (ends-add! (+ 1 i))]
                 [else (touched-add! α)
                       (touch! (+ 1 i) Vₜ)])]
          [(-b '()) (ends-add! i)]
          [_ (set! sound? #f)
             (ends-add! i)])))

    (define Ws (for/set: : W^ ([n (in-ends)])
                 (for/list : W ([i (in-range n)]) (hash-ref elems i))))
    (values Ws sound?))

  (: inst-∀/C : Σ (Pairof -l -l) ∀/C α ℓ → R)
  ;; Monitor function against freshly instantiated parametric contract
  (define (inst-∀/C Σ₀ ctx G α ℓ)
    (match-define (∀/C xs c (and αₒ (α:dyn (β:clo ℓₒ) _))) G)
    (match-define (cons l+ (and l- l-seal)) ctx)
    (define Γ* (Σ@/env αₒ Σ₀))
    (define ΔΣ:seals
      (for/fold ([acc : ΔΣ ⊥ΔΣ]) ([x (in-list xs)])
        (define αₓ (α:dyn (β:sealed x ℓ) H₀))
        (⧺ acc
           (alloc αₓ ∅)
           (alloc-lex Σ₀ x {set (Seal/C αₓ l-seal)}))))
    (define Σ₁ (⧺ (cons (car Σ₀) Γ*) ΔΣ:seals))
    (with-each-path ([(ΔΣ₁ W:c) (evl Σ₁ c)])
      (ΔΣ⧺R (⧺ ΔΣ:seals ΔΣ₁)
            (mon (⧺ Σ₁ ΔΣ₁) (Ctx l+ l- ℓₒ ℓ) (car W:c) (Σ@ α Σ₀)))))
  (define-simple-macro (with-guarded-arity W f ℓ [p body ...] ...)
    (match W
      [p body ...] ...
      [_ (err! (Err:Arity f (length W) ℓ)) ⊥R]))
  )
