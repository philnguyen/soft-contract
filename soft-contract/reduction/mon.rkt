#lang typed/racket/base

(provide mon@)

(require racket/match
         racket/set
         syntax/parse/define
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit mon@
  (import compile^ app^ kont^ proof-system^ local-prover^ widening^ prims^
          env^ sto^ val^ instr^ pc^ pretty-print^)
  (export mon^)

  (: mon : -l³ -ℒ -W¹ -W¹ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon l³ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #;(printf "mon: ~a on ~a~n - l+: ~a~n" (show-W¹ W-C) (show-W¹ W-V) (-l³-pos l³))
    (match-define (-W¹ C _) W-C)
    (define mon₁
      (cond
        [(-=>_? C) mon-=>_]
        [(-St/C? C) mon-struct/c]
        [(-x/C? C) mon-x/c]
        [(-And/C? C) mon-and/c]
        [(-Or/C? C) mon-or/c]
        [(-Not/C? C) mon-not/c]
        [(-One-Of/C? C) mon-one-of/c]
        [(-Vectorof? C) mon-vectorof]
        [(-Vector/C? C) mon-vector/c]
        [(-Hash/C? C) mon-hash/c]
        [else mon-flat/c]))
    (mon₁ l³ ℒ W-C W-V Γ ⟪ℋ⟫ Σ ⟦k⟧))

  (define (mon-=>_ [l³ : -l³] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-W¹ (? -=>_? grd) c) W-C)
    (match-define (-W¹ V v) W-V)
    (match-define (-l³ l+ _ lo) l³)
    (define σ (-Σ-σ Σ))

    (: blm : -V → -Γ → (℘ -ς))
    (define ((blm C) Γ)
      (define blm (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)))
      (⟦k⟧ blm Γ ⟪ℋ⟫ Σ))

    (: chk-arity : -Γ → (℘ -ς))
    (define (chk-arity Γ)
      (define W-grd-arity
        (let* ([a (guard-arity grd)]
               [b (-b a)])
          (-W¹ b b)))
      (define W-arity
        (let ([A (V-arity V)]
              [a (?t@ 'procedure-arity v)])
          (-W¹ (if A (-b A) (+●)) a)))
      (with-Γ+/-oW (σ Γ 'arity-includes? W-arity W-grd-arity)
        #:on-t wrap
        #:on-f (let ([C (match W-grd-arity
                          [(-W¹ (-b (? integer? n)) _)
                           (format-symbol "(arity-includes/c ~a)" n)]
                          [(-W¹ (-b (arity-at-least n)) _)
                           (format-symbol "(arity-at-least/c ~a)" n)])])
                 (blm C))))

    (: wrap : -Γ → (℘ -ς))
    (define (wrap Γ)
      (define ⟪α⟫
        (-α->⟪α⟫
             (cond
               [(-●? V) (-α.fn.●)] ; hack to reduce unneccessary splits
               [else
                (define φs ; hack for functional OO programs...
                  (for/set: : (℘ -t) ([φ (in-set (-Γ-facts Γ))]
                                      #:when (match? φ (-t.@ (? op-≡?) (list (? -x?) (? -b?)))))
                    φ))
                (define v*
                  (match V
                    [(-Clo fml ⟦e⟧ _ _) ⟦e⟧]
                    [_ v]))
                (-α.fn v* ℒ ⟪ℋ⟫ l+ φs)])))
      (define Ar (-Ar grd ⟪α⟫ l³))

      (σ⊕! Σ Γ ⟪α⟫ W-V)
      (define v* ; hack
        (match v
          [(-t.@ (-ar.mk) (== c)) v]
          [_ (?t@ (-ar.mk) c v)]))
      (⟦k⟧ (-W (list Ar) v*) Γ ⟪ℋ⟫ Σ))

    (with-Γ+/-oW (σ Γ 'procedure? W-V)
      #:on-t chk-arity
      #:on-f (blm 'procedure?)))

  (define (mon-struct/c [l³ : -l³] [ℒ : -ℒ] [Wₚ : -W¹] [Wᵥ : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-W¹ (and Vₚ (-St/C flat? 𝒾 αℓs)) sₚ) Wₚ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-l³ l+ _ lo) l³)
    (define σ (-Σ-σ Σ))
    (define p (-st-p 𝒾))

    (: chk-fields : → (℘ -ς))
    (define (chk-fields)
      (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
      (define all-immutable? (struct-all-immutable? 𝒾))
      
      (define ⟦field⟧s : (Listof -⟦e⟧)
        (let ([Wᵥ* (-W¹ (V+ σ Vᵥ Vₚ) sᵥ)])
          (for/list ([α (in-list αs)]
                     [i (in-naturals)] #:when (index? i))
            (define ac (-st-ac 𝒾 i))
            (mk-app (ℒ-with-l ℒ 'mon-struct/c) (mk-rt (-W¹ ac #f)) (list (mk-rt Wᵥ*))))))

      (cond
        [(null? ⟦field⟧s)
         (⟦k⟧ (-W (list (-St 𝒾 '())) sᵥ) Γ ⟪ℋ⟫ Σ)]
        [else
         (define cs (-struct/c-split sₚ 𝒾))
         (define K (let ([k (-st-mk 𝒾)]) (-W¹ k k)))
         (define ⟦k⟧* ; maybe wrap the monitored struct
           (cond [all-immutable? ⟦k⟧]
                 [else
                  (define α (-α->⟪α⟫ (-α.st 𝒾 ℒ ⟪ℋ⟫ l+)))
                  (wrap-st∷ 𝒾 sᵥ Vₚ ℒ l³ ⟦k⟧)]))
         (for/union : (℘ -ς) ([Cs (σ@/list Σ αs)])
                    (define ⟦mon⟧s : (Listof -⟦e⟧)
                      (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s] [ℓᵢ : ℓ ℓs])
                        (mk-mon l³ (ℒ-with-mon ℒ ℓᵢ) (mk-rt (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
                    (define ⟦reconstr⟧ (mk-app
                                        ℒ (mk-rt K) ⟦mon⟧s))
                    (⟦reconstr⟧ ⊥ρ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]))

    (with-Γ⊢oW (σ Γ p Wᵥ)
      #:on-t chk-fields
      #:on-f (λ ()
               (define blm (-blm l+ lo (list p) (list Vᵥ) (-ℒ-app ℒ)))
               (⟦k⟧ blm Γ ⟪ℋ⟫ Σ))))

  (define (mon-x/c [l³ : -l³] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-W¹ C c) W-C)
    (match-define (-W¹ V v) W-V)
    (match-define (-x/C ⟪α⟫) C)
    (define x (match-let ([(-α.x/c x*) (⟪α⟫->-α ⟪α⟫)])
                (+x!/memo 'mon x*)))
    (define 𝐱 (-x x))
    (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ ℒ))
    (for/set: : (℘ -ς) ([C* (σ@ Σ ⟪α⟫)])
      (define ⟪α⟫ᵥ (-α->⟪α⟫ (-α.mon-x/c x ⟪ℋ⟫ₑₑ (-l³-pos l³))))
      (define αₖ (-ℳ x l³ (-ℒ ∅eq (-ℒ-app ℒ)) #;ℒ C* ⟪α⟫ᵥ #|TODO|# ⊤Γ ⟪ℋ⟫ₑₑ))
      (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ v ∅ ∅))
      (σ⊕! Σ Γ ⟪α⟫ᵥ W-V)
      (σₖ⊕! Σ αₖ κ)
      (-ς↑ αₖ)))

  (define (mon-and/c [l³ : -l³] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-W¹ (-And/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)) c) W-C)
    (match-define (list c₁ c₂) (-app-split 'and/c c 2))
    (for/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
               (mon l³ (ℒ-with-mon ℒ ℓ₁) (-W¹ C₁ c₁) W-V Γ ⟪ℋ⟫ Σ 
                    (mon.c∷ l³ (ℒ-with-mon ℒ ℓ₂) (-W¹ C₂ c₂) ⟦k⟧))))

  (define (mon-or/c [l³ : -l³] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ (-Or/C flat? (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)) c) W-C)
    (match-define (list c₁ c₂) (-app-split 'or/c c 2))
    
    (: chk-or/c : -W¹ ℓ -W¹ ℓ → (℘ -ς))
    (define (chk-or/c W-fl ℓ-fl W-ho ℓ-ho)
      (flat-chk lo (ℒ-with-mon ℒ ℓ-fl) W-fl W-V Γ ⟪ℋ⟫ Σ
                (mon-or/c∷ l³ (ℒ-with-mon ℒ ℓ-ho) W-fl W-ho W-V ⟦k⟧)))

    (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
                (define W-C₁ (-W¹ C₁ c₁))
                (define W-C₂ (-W¹ C₂ c₂))
                (cond [(C-flat? C₁) (chk-or/c W-C₁ ℓ₁ W-C₂ ℓ₂)]
                      [(C-flat? C₂) (chk-or/c W-C₂ ℓ₂ W-C₁ ℓ₁)]
                      [else (error 'or/c "No more than 1 higher-order disjunct for now")])))

  (define (mon-not/c [l³ : -l³] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ (and C (-Not/C (-⟪α⟫ℓ α ℓ*))) c) W-C)
    (match-define (-W¹ V _) W-V)
    (match-define (list c*) (-app-split 'not/c c 1))
    (define ⟦k⟧*
      (let ([⟦ok⟧ (mk-rt W-V)]
            [⟦er⟧ (mk-rt (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)))])
        (if∷ lo ⟦er⟧ ⟦ok⟧ ⊥ρ ⟦k⟧)))
    (for/union : (℘ -ς) ([C* (σ@ (-Σ-σ Σ) α)])
               (assert C* C-flat?)
               (define W-C* (-W¹ C* c*))
               (app (ℒ-with-mon ℒ ℓ*) W-C* (list W-V) Γ ⟪ℋ⟫ Σ ⟦k⟧*)))

  (define (mon-one-of/c [l³ : -l³] [ℒ : -ℒ] [Wₚ : -W¹] [Wᵥ : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ (and C (-One-Of/C bs)) _) Wₚ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (define (blm)
      (⟦k⟧ (-blm l+ lo (list C) (list Vᵥ) (-ℒ-app ℒ)) Γ ⟪ℋ⟫ Σ))
    (case (sat-one-of Vᵥ bs)
      [(✓) (⟦k⟧ (-W (list Vᵥ) sᵥ) Γ ⟪ℋ⟫ Σ)]
      [(✗) (blm)]
      [(?) (∪ (for/union : (℘ -ς) ([b bs])
                         (⟦k⟧ (-W (list (-b b)) sᵥ) (Γ+ Γ (?t@ 'equal? sᵥ (-b b))) ⟪ℋ⟫ Σ))
              (blm))]))

  (define (mon-vectorof [l³ : -l³] [ℒ : -ℒ] [Wₚ : -W¹] [Wᵥ : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧])
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ (and Vₚ (-Vectorof (-⟪α⟫ℓ α* ℓ*))) _) Wₚ)
    (define σ (-Σ-σ Σ))

    (: blm : -V → → (℘ -ς))
    (define ((blm C))
      (define blm (-blm l+ lo (list C) (list Vᵥ) (-ℒ-app ℒ)))
      (⟦k⟧ blm Γ ⟪ℋ⟫ Σ))

    (: chk-elems : → (℘ -ς))
    (define (chk-elems)
      (define ⟦ref⟧
        (mk-app (ℒ-with-l ℒ 'mon-vectorof)
                (mk-rt (-W¹ 'vector-ref #f))
                (list (mk-rt Wᵥ)
                      (mk-rt (-W¹ (+● 'exact-nonnegative-integer?) (-x (+x!/memo 'vof-idx)))))))
      (define ⟦k⟧* (mk-wrap-vect∷ sᵥ Vₚ ℒ l³ ⟦k⟧))
      (define c* #f #;(⟪α⟫->s α*))
      (define Wₗ (vec-len σ Γ Wᵥ))
      (for/union : (℘ -ς) ([C* (in-set (σ@ Σ α*))])
                 (define ⟦mon⟧ (mk-mon l³ (ℒ-with-mon ℒ ℓ*) (mk-rt (-W¹ C* c*)) ⟦ref⟧))
                 (⟦mon⟧ ⊥ρ Γ ⟪ℋ⟫ Σ (ap∷ (list Wₗ (+W¹ 'make-vector)) '() ⊥ρ ℒ
                                          ⟦k⟧*))))

    (with-Γ⊢oW (σ Γ 'vector? Wᵥ)
      #:on-t chk-elems
      #:on-f (blm 'vector?)))

  (define (mon-vector/c [l³ : -l³] [ℒ : -ℒ] [Wₚ : -W¹] [Wᵥ : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ (and Vₚ (-Vector/C ⟪α⟫ℓs)) sₚ) Wₚ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (define σ (-Σ-σ Σ))
    (define n (length ⟪α⟫ℓs))
    
    (: blm : -V → → (℘ -ς))
    (define ((blm C))
      (define blm (-blm l+ lo (list C) (list Vᵥ) (-ℒ-app ℒ)))
      (⟦k⟧ blm Γ ⟪ℋ⟫ Σ))

    (: chk-len : → (℘ -ς))
    (define (chk-len)
      (define Wₙ (vec-len σ Γ Wᵥ))
      (define N (let ([bₙ (-b n)]) (-W¹ bₙ bₙ)))
      (with-Γ⊢oW (σ Γ '= Wₙ N)
        #:on-t chk-flds
        #:on-f (blm (format-symbol "vector-length/c ~a" n))))

    (: chk-flds : → (℘ -ς))
    (define (chk-flds)
      (define-values (⟪α⟫s ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc ⟪α⟫ℓs))
      
      (define cs (-app-split 'vector/c sₚ n))

      (for/union : (℘ -ς) ([Cs (in-set (σ@/list σ ⟪α⟫s))])
                 (define ⟦mon-fld⟧s : (Listof -⟦e⟧)
                   (for/list ([Cᵢ (in-list Cs)]
                              [cᵢ (in-list cs)]
                              [ℓᵢ (in-list ℓs)]
                              [i (in-naturals)] #:when (index? i))
                     (define Wᵢ (let ([bᵢ (-b i)]) (-W¹ bᵢ #f)))
                     (define Wₚᵢ (-W¹ Cᵢ cᵢ))
                     (define ⟦ref⟧
                       (mk-app (ℒ-with-l ℒ 'mon-vector/c)
                               (mk-rt (-W¹ 'vector-ref #f))
                               (list (mk-rt Wᵥ) (mk-rt Wᵢ))))
                     (mk-mon l³ (ℒ-with-mon ℒ ℓᵢ) (mk-rt Wₚᵢ) ⟦ref⟧)))
                 
                 (match ⟦mon-fld⟧s
                   ['() (⟦k⟧ (-W (list (-Vector '())) sᵥ) Γ ⟪ℋ⟫ Σ)] ; no need to wrap
                   [(cons ⟦fld⟧₀ ⟦fld⟧s)
                    (define ⟦k⟧* (mk-wrap-vect∷ sᵥ Vₚ ℒ l³ ⟦k⟧))
                    (⟦fld⟧₀ ⊥ρ Γ ⟪ℋ⟫ Σ
                     (ap∷ (list (+W¹ 'vector)) ⟦fld⟧s ⊥ρ ℒ ⟦k⟧*))])))

    (with-Γ⊢oW (σ Γ 'vector? Wᵥ)
      #:on-t chk-len
      #:on-f (blm 'vector?)))

  (define (mon-hash/c [l³ : -l³] [ℒ : -ℒ] [Wₚ : -W¹] [Wᵤ : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ (and Vₚ (-Hash/C (-⟪α⟫ℓ αₖ ℓₖ) (-⟪α⟫ℓ αᵥ ℓᵥ))) sₚ) Wₚ)
    (match-define (-W¹ Vᵤ tᵤ) Wᵤ)
    (define σ (-Σ-σ Σ))
    (define ℓ (-ℒ-app ℒ))

    (: chk-content : → (℘ -ς))
    (define (chk-content)
      (define doms (σ@ Σ αₖ))
      (define rngs (σ@ Σ αᵥ))

      (: chk-key-vals : (℘ -V) (℘ -V) → (℘ -ς))
      (define (chk-key-vals Vsₖ Vsᵥ)
        (define ℒₖ (ℒ-with-mon ℒ ℓₖ))
        (define ℒᵥ (ℒ-with-mon ℒ ℓᵥ))
        (for*/union : (℘ -ς) ([Cᵥ (in-set rngs)] [Vᵥ (in-set Vsᵥ)])
           (define mon-vals (mk-mon l³ ℒᵥ (mk-rt (-W¹ Cᵥ #|TODO|# #f)) (mk-rt (-W¹ Vᵥ #|TODO|# #f))))
           (define wrap
             (let ([αᵤ (-α->⟪α⟫ (-α.unhsh ℒ ⟪ℋ⟫ l+))])
               (mk-rt (-W¹ (-Hash/guard Vₚ αᵤ l³) tᵤ))))
           (define ⟦k⟧* (bgn∷ (list mon-vals wrap) ⊥ρ ⟦k⟧))
          (for*/union : (℘ -ς) ([Cₖ (in-set doms)] [Vₖ (in-set Vsₖ)])
            (mon l³ ℒₖ (-W¹ Cₖ #|TODO|# #f) (-W¹ Vₖ #|TODO|# #f) Γ ⟪ℋ⟫ Σ ⟦k⟧*))))
      
      (match Vᵤ
        [(-Hash/guard _ αᵤ _)
         (define-values (Vsₖ Vsᵥ) (collect-hash-pairs σ αᵤ))
         (chk-key-vals Vsₖ Vsᵥ)]
        [(-Hash^ α₁ α₂ _)
         (chk-key-vals (σ@ Σ α₁) (σ@ Σ α₂))]
        [_
         (∪ (⟦k⟧ (W¹->W Wᵤ) Γ ⟪ℋ⟫ Σ)
            (for/union : (℘ -ς) ([C (in-set (∪ doms rngs))])
              (⟦k⟧ (-blm l+ lo (list C) (list (+●)) ℓ) Γ ⟪ℋ⟫ Σ)))]))

    (with-Γ⊢oW (σ Γ 'hash? Wᵤ)
      #:on-t chk-content
      #:on-f (λ ()
               (define blm (-blm l+ lo '(hash?) (list Vᵤ) ℓ))
               (⟦k⟧ blm Γ ⟪ℋ⟫ Σ))))

  (define (mon-flat/c [l³ : -l³] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (match-define (-l³ l+ _ lo) l³)
    (match-define (-W¹ C c) W-C)
    (match-define (-W¹ V v) W-V)
    (define cv (and (-h? c) (?t@ c v)))
    (case (Γ⊢V∈C (-Σ-σ Σ) Γ W-V W-C)
      [(✓) (⟦k⟧ (-W (list V) v) Γ ⟪ℋ⟫ Σ)]
      [(✗) (⟦k⟧ (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)) Γ ⟪ℋ⟫ Σ)]
      [(?)
       (define V* (V+ (-Σ-σ Σ) V C))
       (app ℒ W-C (list W-V) Γ ⟪ℋ⟫ Σ
            (if.flat/c∷ (-W (list V*) v) (-blm l+ lo (list C) (list V) (-ℒ-app ℒ)) ⟦k⟧))]))

  (define (flat-chk [l : -l] [ℒ : -ℒ] [W-C : -W¹] [W-V : -W¹] [Γ : -Γ] [⟪ℋ⟫ : -⟪ℋ⟫] [Σ : -Σ] [⟦k⟧ : -⟦k⟧]) : (℘ -ς)
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ C c) W-C)
    (match-define (-W¹ V v) W-V)
    (match C
      [(-And/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (match-define (list c₁ c₂) (-app-split 'and/c c 2))
       [for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
                   (define W-C₁ (-W¹ C₁ c₁))
                   (define W-C₂ (-W¹ C₂ c₂))
                   (flat-chk l (ℒ-with-mon ℒ ℓ₁) W-C₁ W-V Γ ⟪ℋ⟫ Σ
                             (fc-and/c∷ l (ℒ-with-mon ℒ ℓ₂) W-C₁ W-C₂ ⟦k⟧))]]
      [(-Or/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (match-define (list c₁ c₂) (-app-split 'or/c c 2))
       (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
                   (define W-C₁ (-W¹ C₁ c₁))
                   (define W-C₂ (-W¹ C₂ c₁))
                   (flat-chk l (ℒ-with-mon ℒ ℓ₁) W-C₁ W-V Γ ⟪ℋ⟫ Σ
                             (fc-or/c∷ l (ℒ-with-mon ℒ ℓ₂) W-C₁ W-C₂ W-V ⟦k⟧)))]
      [(-Not/C (-⟪α⟫ℓ α ℓ*))
       (match-define (list c*) (-app-split 'not/c c 1))
       (for/union : (℘ -ς) ([C* (σ@ Σ α)])
                  (define W-C* (-W¹ C* c*))
                  (flat-chk l (ℒ-with-mon ℒ ℓ*) W-C* W-V Γ ⟪ℋ⟫ Σ
                            (fc-not/c∷ l W-C* W-V ⟦k⟧)))]
      [(-One-Of/C bs)
       (case (sat-one-of V bs)
         [(✓) (⟦k⟧ (-W (list -tt V) (?t@ 'values -tt v)) Γ ⟪ℋ⟫ Σ)]
         [(✗) (⟦k⟧ (+W (list -ff)) Γ ⟪ℋ⟫ Σ)]
         [(?)
          (∪
           (for/union : (℘ -ς) ([b bs])
                      (define v (-b b))
                      (⟦k⟧ (-W (list -ff v) (?t@ 'values -tt v)) Γ ⟪ℋ⟫ Σ))
           (⟦k⟧ (+W (list -ff)) Γ ⟪ℋ⟫ Σ))])]
      [(-St/C _ s αℓs)
       (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
       (define cs (-struct/c-split c s))
       (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
                  (define ⟦chk-field⟧s : (Listof -⟦e⟧)
                    (for/list ([Cᵢ (in-list Cs)]
                               [cᵢ (in-list cs)]
                               [ℓᵢ : ℓ (in-list ℓs)]
                               [i (in-naturals)] #:when (index? i))
                      (define ac (-st-ac s i))
                      (define ⟦ref⟧ᵢ (mk-app (ℒ-with-l ℒ 'fc) (mk-rt (-W¹ ac ac)) (list (mk-rt W-V))))
                      (mk-fc l (ℒ-with-mon ℒ ℓᵢ) (mk-rt (-W¹ Cᵢ cᵢ)) ⟦ref⟧ᵢ)))
                  (match ⟦chk-field⟧s
                    ['()
                     (define p (-st-p s))
                     (define ⟦rt⟧ (mk-rt (-W (list -tt (V+ σ V p)) (?t@ 'values -tt v))))
                     (app ℒ (-W¹ p p) (list W-V) Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ (↓ₚᵣₘ -ff) ⊥ρ ⟦k⟧))]
                    [(cons ⟦chk-field⟧ ⟦chk-field⟧s*)
                     (⟦chk-field⟧ ⊥ρ Γ ⟪ℋ⟫ Σ
                      (fc-struct/c∷ l ℒ s '() ⟦chk-field⟧s* ⊥ρ ⟦k⟧))]))]
      [(-x/C ⟪α⟫)
       (define x (match-let ([(-α.x/c x*) (⟪α⟫->-α ⟪α⟫)])
                   (+x!/memo 'fc x*)))
       (define 𝐱 (-x x))
       (define ⟪ℋ⟫ₑₑ (⟪ℋ⟫+ ⟪ℋ⟫ ℒ))
       (for/set: : (℘ -ς) ([C* (σ@ Σ ⟪α⟫)])
         (define ⟪α⟫ᵥ (-α->⟪α⟫ (-α.fc-x/c x ⟪ℋ⟫)))
         (define αₖ (-ℱ x l (-ℒ ∅eq (-ℒ-app ℒ)) #;ℒ C* ⟪α⟫ᵥ #|TODO|# ⊤Γ ⟪ℋ⟫ₑₑ))
         (define κ (-κ ⟦k⟧ Γ ⟪ℋ⟫ v ∅ ∅))
         (σ⊕! Σ Γ ⟪α⟫ᵥ W-V)
         (σₖ⊕! Σ αₖ κ)
         (-ς↑ αₖ))]
      [_
       (define ⟦ap⟧ (mk-app (ℒ-with-l ℒ 'fc) (mk-rt W-C) (list (mk-rt W-V))))
       (define ⟦rt⟧ (mk-rt (-W (list -tt (V+ σ V C)) (?t@ 'values -tt v))))
       (⟦ap⟧ ⊥ρ Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ (↓ₚᵣₘ -ff) ⊥ρ ⟦k⟧))]))

  (define (vec-len [σ : -σ] [Γ : -Γ] [W : -W¹]) : -W¹
    (match-define (-W¹ V s) W)
    (define ?n : (Option Natural)
      (match V
        [(-Vector ⟪α⟫s) (length ⟪α⟫s)]
        [(-Vector^ _ V)
         (match V
           [(-b (? exact-nonnegative-integer? n)) n]
           [_ #f])]
        [(-Vector/guard grd _ _)
         (match grd
           [(-Vector/C ⟪α⟫s) (length ⟪α⟫s)]
           [_ #f])]
        [_ #f]))
    (define Vₙ (if ?n (-b ?n) (+● 'exact-nonnegative-integer?)))
    (-W¹ Vₙ (?t@ 'vector-length s)))

  ;; FIXME Duplicate macros
  (define-simple-macro (with-Γ+/-oW (σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
    (Γ+/-oW/handler on-t on-f σ Γ o W ...))
  (define-simple-macro (with-Γ⊢oW (σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
    (Γ⊢oW/handler on-t on-f σ Γ o W ...))
  )
