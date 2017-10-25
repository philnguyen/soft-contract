#lang typed/racket/base

(provide mon@)

(require racket/sequence
         racket/match
         racket/set
         syntax/parse/define
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit mon@
  (import static-info^
          compile^ app^ kont^ proof-system^ path^ prims^ fc^
          env^ sto^ val^ instr^ pretty-print^ for-gc^ (prefix r: prim-runtime^))
  (export mon^)

  (: mon : -ctx -V^ -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon ctx C^ V^ H φ Σ ⟦k⟧)
    (for/union : (℘ -ς) ([C (in-set C^)])
      (cond [(-=>_? C) (mon-=>_ ctx C V^ H φ Σ ⟦k⟧)]
            [(-St/C? C) (mon-struct/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-x/C? C) (mon-x/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-And/C? C) (mon-and/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-Or/C? C) (mon-or/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-Not/C? C) (mon-not/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-One-Of/C? C) (mon-one-of/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-Vectorof? C) (mon-vectorof ctx C V^ H φ Σ ⟦k⟧)]
            [(-Vector/C? C) (mon-vector/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-Hash/C? C) (mon-hash/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-Set/C? C) (mon-set/c ctx C V^ H φ Σ ⟦k⟧)]
            [(-Seal/C? C) (mon-seal/c ctx C V^ H φ Σ ⟦k⟧)]
            [else (mon-flat/c ctx C V^ H φ Σ ⟦k⟧)])))

  (: mon-=>_ : -ctx -=>_ -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-=>_ ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (define σ (-Σ-σ Σ))

    (: blm : -V → -φ → (℘ -ς))
    (define ((blm C) φ)
      (define blm (blm/simp l+ lo (list {set C}) (list V^) ℓ))
      (⟦k⟧ blm H φ Σ))

    (: chk-arity : -φ → (℘ -ς))
    (define (chk-arity φ)
      (define grd-arity (-b (guard-arity C)))
      (define val-arity
        (for/set: : (℘ -V) ([V (in-set V^)])
          (cond [(V-arity V) => -b]
                [(-t? V) (-t.@ 'procedure-arity (list V))]
                [else (-● {set 'procedure-arity?})])))
      (with-φ+/-oV (σ φ 'arity-includes? val-arity {set grd-arity})
        #:on-t wrap
        #:on-f (blm (match grd-arity
                      [(-b (? integer? n))
                       (format-symbol "(arity-includes/c ~a)" n)]
                      [(-b (arity-at-least n))
                       (format-symbol "(arity-at-least/c ~a)" n)]
                      [(-b (list n ...))
                       (string->symbol (format "(arity in ~a)" n))]))))

    (: wrap : -φ → (℘ -ς))
    (define (wrap φ)
      (define-values (V^* α)
        (cond [(sequence-andmap -●? V^)
               ;; TODO see if this helps or worsens zombie's state space
               (define V (-Fn● (guard-arity C) '†))
               (values {set V} (-α->⟪α⟫ (-α.imm V)))]
              [else
               (values V^ (-α->⟪α⟫ (-α.fn ctx H)))]))
      (define φ* (φ⊔ φ α V^*))
      (define Ar (-Ar C α ctx))
      (⟦k⟧ (list {set Ar}) H φ* Σ))

    (with-φ+/-oV (σ φ 'procedure? V^)
      #:on-t (if (-∀/C? C) wrap chk-arity)
      #:on-f (blm 'procedure?)))

  (: mon-struct/c : -ctx -St/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-struct/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓₘ) ctx)
    (match-define (-St/C flat? 𝒾 αℓs) C)
    (define σ (-Σ-σ Σ))
    (define p (-st-p 𝒾))

    (: chk-fields : -φ → (℘ -ς))
    (define (chk-fields φ)
      (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
      (define all-immutable? (struct-all-immutable? 𝒾))
      (define ⟦field⟧s : (Listof -⟦e⟧)
        (let ([V^* (V+ σ φ V^ C)])
          (for/list ([α (in-list αs)]
                     [i (in-naturals)] #:when (index? i))
            (mk-app (ℓ-with-id ℓₘ (list 'mon-struct/c 𝒾 i)) (mk-V (-st-ac 𝒾 i)) (list (mk-A (list V^*)))))))
      (define ⟦mon⟧s : (Listof -⟦e⟧)
        (for/list ([Cᵢ (σ@/list Σ (-φ-cache φ) αs)] [⟦field⟧ᵢ ⟦field⟧s] [ℓᵢ : ℓ ℓs])
          (mk-mon (ctx-with-ℓ ctx ℓᵢ) (mk-A (list Cᵢ)) ⟦field⟧ᵢ)))
      (define ⟦reconstr⟧ (mk-app ℓₘ (mk-V (-st-mk 𝒾)) ⟦mon⟧s))
      (define ⟦k⟧* (if all-immutable? ⟦k⟧ (wrap-st∷ C ctx ⟦k⟧)))
      (⟦reconstr⟧ ⊥ρ H φ Σ ⟦k⟧*))

    (with-φ+/-oV (σ φ p V^)
      #:on-t chk-fields
      #:on-f (λ ([φ : -φ])
               (define blm (blm/simp l+ lo (list p) (list V^) ℓₘ))
               (⟦k⟧ blm H φ Σ))))

  (: mon-x/c : -ctx -x/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-x/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-x/C α) C)
    (define C^* (σ@ Σ (-φ-cache φ) α))
    (push-mon ctx C^* V^ H φ Σ ⟦k⟧ #:looped #t))

  (: mon-and/c : -ctx -And/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-and/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-And/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)) C)
    (define C₁ (σ@ Σ (-φ-cache φ) α₁))
    (define C₂ (σ@ Σ (-φ-cache φ) α₂))
    (define ⟦k⟧* (mon.c∷ (ctx-with-ℓ ctx ℓ₂) C₂ ⟦k⟧))
    (push-mon (ctx-with-ℓ ctx ℓ₁) C₁ V^ H φ Σ ⟦k⟧*))

  (: mon-or/c : -ctx -Or/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-or/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo _) ctx)
    (match-define (-Or/C flat? (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)) C)

    (: chk-or/c : -V^ -ctx -V^ -ctx → (℘ -ς))
    (define (chk-or/c C-fl ctx-fl C-ho ctx-ho)
      (match-define (-ctx _ _ lo-fl ℓ-fl) ctx-fl)
      (push-fc lo-fl ℓ-fl C-fl V^ H φ Σ
               (mon-or/c∷ ctx-ho C-fl C-ho V^ ⟦k⟧)))

    (define C₁ (σ@ Σ (-φ-cache φ) α₁))
    (define C₂ (σ@ Σ (-φ-cache φ) α₂))
    (cond [(C^-flat? C₁) (chk-or/c C₁ (ctx-with-ℓ ctx ℓ₁) C₂ (ctx-with-ℓ ctx ℓ₂))]
          [(C^-flat? C₂) (chk-or/c C₂ (ctx-with-ℓ ctx ℓ₂) C₁ (ctx-with-ℓ ctx ℓ₁))]
          [else (error 'or/c "No more than 1 higher-order disjunct for now")]))

  (: mon-not/c : -ctx -Not/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-not/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Not/C (-⟪α⟫ℓ α ℓ*)) C)
    (define ⟦k⟧*
      (let ([⟦ok⟧ (mk-A (list V^))]
            [⟦er⟧ (mk-A (blm/simp l+ lo (list {set C}) (list V^) ℓ))])
        (if∷ lo ⟦er⟧ ⟦ok⟧ ⊥ρ ⟦k⟧)))
    (define C*^ (σ@ (-Σ-σ Σ) (-φ-cache φ) α))
    (app ℓ* C*^ (list V^) H φ Σ ⟦k⟧*))

  (: mon-one-of/c : -ctx -One-Of/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-one-of/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-One-Of/C bs) C)
    (define (blm) (⟦k⟧ (blm/simp l+ lo (list {set C}) (list V^) ℓ) H φ Σ))
    (case (sat-one-of V^ bs)
      [(✓) (⟦k⟧ (list V^) H φ Σ)]
      [(✗) (blm)]
      [(?) (∪ (⟦k⟧ (list (list->set (set-map bs -b))) H φ Σ) (blm))]))

  (: mon-vectorof : -ctx -V -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-vectorof ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Vectorof (-⟪α⟫ℓ α* ℓ*)) C)
    (define σ (-Σ-σ Σ))

    (: blm : -h → -φ → (℘ -ς))
    (define ((blm C) φ)
      (define blm (blm/simp l+ lo (list C) (list V^) ℓ))
      (⟦k⟧ blm H φ Σ))

    (: chk-elems : -φ → (℘ -ς))
    (define (chk-elems φ)
      (define V^* (V+ σ φ V^ C))
      (define ⟦ref⟧
        (mk-app (ℓ-with-id ℓ (list 'mon-vectorof))
                (mk-V 'vector-ref)
                (list (mk-A (list V^*)) (mk-V (-● {set 'exact-nonnegative-integer?})))))
      (define ⟦k⟧* (mk-wrap-vect∷ C ctx ⟦k⟧))
      (define Vₗ^ (vec-len σ φ V^*))
      (define C*^ (σ@ Σ (-φ-cache φ) α*))
      (define ⟦mon⟧ (mk-mon (ctx-with-ℓ ctx ℓ*) (mk-A (list C*^)) ⟦ref⟧))
      (⟦mon⟧ ⊥ρ H φ Σ (ap∷ (list Vₗ^ {set 'make-vector}) '() ⊥ρ ℓ ⟦k⟧*)))

    (with-φ+/-oV (σ φ 'vector? V^)
      #:on-t chk-elems
      #:on-f (blm 'vector?)))

  (: mon-vector/c : -ctx -Vector/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-vector/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Vector/C ⟪α⟫ℓs) C)
    (define σ (-Σ-σ Σ))
    (define n (length ⟪α⟫ℓs))
    
    (: blm : -h → -φ → (℘ -ς))
    (define ((blm C) φ)
      (define blm (blm/simp l+ lo (list C) (list V^) ℓ))
      (⟦k⟧ blm H φ Σ))

    (: chk-len : -φ → (℘ -ς))
    (define (chk-len φ)
      (define Vₙ^ (vec-len σ φ V^))
      (with-φ+/-oV (σ φ '= Vₙ^ {set (-b n)})
        #:on-t chk-flds
        #:on-f (blm (format-symbol "vector-length/c ~a" n))))

    (: chk-flds : -φ → (℘ -ς))
    (define (chk-flds φ)
      (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc ⟪α⟫ℓs))
      (define V^* (V+ σ φ V^ C))
      (define Cs (σ@/list σ (-φ-cache φ) αs))
      (define ⟦mon-fld⟧s : (Listof -⟦e⟧)
        (for/list ([Cᵢ (in-list Cs)] [ℓᵢ (in-list ℓs)] [i (in-naturals)] #:when (index? i))
          (define ⟦ref⟧
            (mk-app (ℓ-with-id ℓ (list 'mon-vector/c i))
                    (mk-V 'vector-ref)
                    (list (mk-A (list V^*)) (mk-V (-b i)))))
          (mk-mon (ctx-with-ℓ ctx ℓᵢ) (mk-A (list Cᵢ)) ⟦ref⟧)))
      
      (match ⟦mon-fld⟧s
        ['() (⟦k⟧ (list {set (-Vector '())}) H φ Σ)] ; no need to wrap
        [(cons ⟦fld⟧₀ ⟦fld⟧s)
         (define ⟦k⟧* (mk-wrap-vect∷ C ctx ⟦k⟧))
         (⟦fld⟧₀ ⊥ρ H φ Σ
                 (ap∷ (list {set 'vector}) ⟦fld⟧s ⊥ρ ℓ ⟦k⟧*))]))

    (with-φ+/-oV (σ φ 'vector? V^)
      #:on-t chk-len
      #:on-f (blm 'vector?)))

  (: mon-hash/c : -ctx -Hash/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-hash/c ctx C Vᵤ^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Hash/C (-⟪α⟫ℓ αₖ ℓₖ) (-⟪α⟫ℓ αᵥ ℓᵥ)) C)
    (define σ (-Σ-σ Σ))

    (: chk-content : -φ → (℘ -ς))
    (define (chk-content φ)
      (define αₕ (-α->⟪α⟫ (-α.unhsh ctx H)))
      
      (: chk-key-vals : -V^ -V^ → (℘ -ς))
      (define (chk-key-vals Vₖ^ Vᵥ^)
        (define wrap (mk-wrapped-hash C ctx αₕ (V+ σ φ Vᵤ^ 'hash?)))
        (cond ;; FIXME hacks for now
          [(or (set-empty? Vₖ^) (set-empty? Vᵥ^))
           (wrap ⊥ρ H φ Σ ⟦k⟧)]
          [else
           (define doms (σ@ Σ (-φ-cache φ) αₖ))
           (define rngs (σ@ Σ (-φ-cache φ) αᵥ))
           (define mon-vals (mk-mon (ctx-with-ℓ ctx ℓᵥ) (mk-A (list rngs)) (mk-A (list Vᵥ^))))
           (define ⟦k⟧* (bgn∷ (list mon-vals wrap) ⊥ρ ⟦k⟧))
           (push-mon (ctx-with-ℓ ctx ℓₖ) doms Vₖ^ H φ Σ ⟦k⟧*)]))

      (for/union : (℘ -ς) ([Vᵤ (in-set Vᵤ^)])
        (match Vᵤ^
          [(? -Hash/guard?)
           ;; havoc would be expensive. Just wrap it for now
           (define φ* (φ⊔ φ αₕ Vᵤ^))
           (⟦k⟧ (list {set (-Hash/guard C αₕ ctx)}) H φ* Σ)]
          [(-Hash^ α₁ α₂ _)
           (chk-key-vals (σ@ Σ (-φ-cache φ) α₁) (σ@ Σ (-φ-cache φ) α₂))]
          [_
           (define ●s {set (-● ∅)})
           (chk-key-vals ●s ●s)])))

    (with-φ+/-oV (σ φ 'hash? Vᵤ^)
      #:on-t chk-content
      #:on-f (λ ([φ : -φ])
               (define blm (blm/simp l+ lo '(hash?) (list Vᵤ^) ℓ))
               (⟦k⟧ blm H φ Σ))))

  (: mon-set/c : -ctx -Set/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-set/c ctx C Vᵤ^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-Set/C (-⟪α⟫ℓ αₑ ℓₑ)) C)
    (define σ (-Σ-σ Σ))

    (: chk-content : -φ → (℘ -ς))
    (define (chk-content φ)
      (define αₛ (-α->⟪α⟫ (-α.unset ctx H)))

      (: chk-elems : -V^ → (℘ -ς))
      (define (chk-elems Vs)
        (define wrap (mk-wrapped-set C ctx αₛ (V+ σ φ Vᵤ^ 'set?)))
        (cond
          [(set-empty? Vs)
           (wrap ⊥ρ H φ Σ ⟦k⟧)]
          [else
           (define ⟦k⟧* (bgn∷ (list wrap) ⊥ρ ⟦k⟧))
           (push-mon (ctx-with-ℓ ctx ℓₑ) (σ@ σ (-φ-cache φ) αₑ) Vs H φ Σ ⟦k⟧*)]))

      (for/union : (℘ -ς) ([Vᵤ (in-set Vᵤ^)])
        (match Vᵤ
          [(? -Set/guard?)
           (define φ* (φ⊔ φ αₛ Vᵤ))
           (⟦k⟧ (list {set (-Set/guard C αₛ ctx)}) H φ* Σ)]
          [(-Set^ α _) (chk-elems (σ@ σ (-φ-cache φ) α))]
          [_ (chk-elems {set (-● ∅)})])))

    (with-φ+/-oV (σ φ 'set? Vᵤ^)
      #:on-t chk-content
      #:on-f (λ ([φ : -φ])
               (define blm (blm/simp l+ lo '(set?) (list Vᵤ^) ℓ))
               (⟦k⟧ blm H φ Σ))))

  (: mon-seal/c : -ctx -Seal/C -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-seal/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-Seal/C x H l) C)
    (match-define (-ctx l+ l- lo ℓ) ctx)
    (define α (-α->⟪α⟫ (-α.sealed x H)))
    (cond
      [(equal? l l+) ; seal
       (define φ* (φ⊔ φ α V^))
       (⟦k⟧ (list {set (-Sealed α)}) H φ* Σ)]
      [(equal? l l-) ; unseal
       (define (blm) (⟦k⟧ (blm/simp l+ lo (list {set C}) (list V^) ℓ) H φ Σ))
       (define (ok) (⟦k⟧ (list (σ@ Σ (-φ-cache φ) α)) H φ Σ))
       (for/union : (℘ -ς) ([V (in-set V^)])
         (match V
           [(-Sealed (== α)) (ok)] ; TODO possible false negs from finite seals
           [(-● _) (∪ (blm) (ok))]
           [_ (blm)]))]
      [else
       (error 'mon-seal/c "seal labeled ~a in context ~a, ~a, ~a" l l+ l- lo)]))

  (: mon-flat/c : -ctx -V -V^ -H -φ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon-flat/c ctx C V^ H φ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (define (blm) (blm/simp l+ lo (list {set C}) (list V^) ℓ))
    (case (V∈C (-Σ-σ Σ) φ V^ C)
      [(✓) (⟦k⟧ (list V^) H φ Σ)]
      [(✗) (⟦k⟧ (blm) H φ Σ)]
      [(?)
       (define V^* (V+ (-Σ-σ Σ) φ V^ C))
       (define ⟦k⟧* (if.flat/c∷ V^* (blm) ⟦k⟧))
       (match C
         [(? -b? b) (app ℓ {set 'equal?} (list V^ {set b}) H φ Σ ⟦k⟧*)]
         [_         (app ℓ {set C      } (list V^        ) H φ Σ ⟦k⟧*)])]))

  (: push-mon ((-ctx -V^ -V^ -H -φ -Σ -⟦k⟧) (#:looped Boolean) . ->* . (℘ -ς)))
  (define (push-mon ctx C^ V^ H φ Σ ⟦k⟧ #:looped [looped? #f])
    (if looped?
        (let ([αₖ (-αₖ H (-M ctx C^ V^) φ)])
          {set (-ς↑ (σₖ+! Σ αₖ ⟦k⟧))})
        (mon ctx C^ V^ H φ Σ ⟦k⟧))) 

  (: vec-len : -σ -φ -V^ → -V^)
  (define (vec-len σ φ V^)
    (for/set: : -V^ ([V (in-set V^)])
      (match V
        [(-Vector αs) (-b (length αs))]
        [(-Vector^ _ (? -b? b)) b]
        [(-Vector/guard (-Vector/C αs) _ _) (-b (length αs))]
        [(? -t? V) (-t.@ 'vector-length (list V))]
        [_ (-● {set 'exact-nonnegative-integer?})])))
  
  ;; FIXME Duplicate macros
  (define-simple-macro (with-φ+/-oV (σ:expr φ:expr o:expr V:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
    (φ+/-oV/handler on-t on-f σ φ o V ...))
  )
