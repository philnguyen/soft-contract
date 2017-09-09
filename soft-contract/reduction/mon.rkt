#lang typed/racket/base

(provide mon@)

(require racket/match
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
          compile^ app^ kont^ proof-system^ local-prover^ widening^ prims^
          env^ sto^ val^ instr^ pc^ pretty-print^ for-gc^ (prefix r: prim-runtime^))
  (export mon^)

  (: mon : -ctx -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  (define (mon ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    #;(printf "mon: ~a on ~a~n - l+: ~a~n" (show-W¹ W-C) (show-W¹ W-V) (-ctx-pos ctx))
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
        [(-Set/C? C) mon-set/c]
        [(-Seal/C? C) mon-seal/c]
        [else mon-flat/c]))
    (mon₁ ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧))

  (:* mon-=>_ mon-struct/c mon-x/c mon-and/c mon-or/c mon-not/c mon-one-of/c
      mon-vectorof mon-vector/c mon-hash/c mon-set/c mon-seal/c mon-flat/c
      : -ctx -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))

  (define (mon-=>_ ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-W¹ (? -=>_? grd) c) W-C)
    (match-define (-W¹ V v) W-V)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (define σ (-Σ-σ Σ))

    (: blm : -V → -Γ → (℘ -ς))
    (define ((blm C) Γ)
      (define blm (-blm l+ lo (list C) (list V) ℓ))
      (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

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
      (define-values (V* ⟪α⟫)
        (match V
          [(? -●?)
           (define V (-Fn● (guard-arity grd)))
           (values V (-α->⟪α⟫ (-α.imm V)))]
          [_
           (define α
             (let ([φs ; hack for functional OO programs...
                    (for/set: : -Γ ([φ (in-set Γ)]
                                    #:when (match? φ (-t.@ (? op-≡?) (list (? -x?) (? -b?)))))
                      φ)]
                   [⟦e⟧
                    (match V
                      [(-Clo fml ⟦e⟧ _ _) ⟦e⟧]
                      [_ #f])])
               (-α->⟪α⟫ (-α.fn ⟦e⟧ ctx ⟪ℋ⟫ φs))))
           (values V α)]))
      (define Ar (-Ar grd ⟪α⟫ ctx))
      (σ⊕! Σ Γ ⟪α⟫ (-W¹ V* v)) ;; TODO??
      (define v* ; hack
        (match v
          [(-t.@ (-ar.mk) (== c)) v]
          [_ (?t@ (-ar.mk) c v)]))
      (⟦k⟧ (-W (list Ar) v*) $ Γ ⟪ℋ⟫ Σ))

    (with-Γ+/-oW (σ Γ 'procedure? W-V)
      #:on-t (if (-∀/C? grd) wrap chk-arity)
      #:on-f (blm 'procedure?)))

  (define (mon-struct/c ctx Wₚ Wᵥ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓₘ) ctx)
    (match-define (-W¹ (and Vₚ (-St/C flat? 𝒾 αℓs)) sₚ) Wₚ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
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
            (mk-app ℓₘ (mk-rt (-W¹ ac #|TODO make sure doesn't explode|# ac)) (list (mk-rt Wᵥ*))))))

      (cond
        [(null? ⟦field⟧s)
         (⟦k⟧ (-W (list (-St 𝒾 '())) sᵥ) $ Γ ⟪ℋ⟫ Σ)]
        [else
         (define cs (-struct/c-split sₚ 𝒾))
         (define K (let ([k (-st-mk 𝒾)]) (-W¹ k k)))
         (define ⟦k⟧* ; maybe wrap the monitored struct
           (cond [all-immutable? ⟦k⟧]
                 [else
                  (define α (-α->⟪α⟫ (-α.st 𝒾 ctx ⟪ℋ⟫)))
                  (wrap-st∷ 𝒾 sᵥ Vₚ ctx ⟦k⟧)]))
         (for/union : (℘ -ς) ([Cs (σ@/list Σ αs)])
                    (define ⟦mon⟧s : (Listof -⟦e⟧)
                      (for/list ([Cᵢ Cs] [cᵢ cs] [⟦field⟧ ⟦field⟧s] [ℓᵢ : ℓ ℓs])
                        (mk-mon (ctx-with-ℓ ctx ℓᵢ) (mk-rt (-W¹ Cᵢ cᵢ)) ⟦field⟧)))
                    (define ⟦reconstr⟧ (mk-app ℓₘ (mk-rt K) ⟦mon⟧s))
                    (⟦reconstr⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]))

    (with-Γ⊢oW (σ Γ p Wᵥ)
      #:on-t chk-fields
      #:on-f (λ ()
               (define blm (-blm l+ lo (list p) (list Vᵥ) ℓₘ))
               (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))))

  (define (mon-x/c ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-W¹ (-x/C ⟪α⟫) _) W-C)
    (define αₓ (cast (⟪α⟫->-α ⟪α⟫) -α.rec-ref))
    (for/union : (℘ -ς) ([C* (σ@ Σ ⟪α⟫)])
      (push-mon ctx (-W¹ C* #f) W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧ #:looped αₓ)))

  (define (mon-and/c ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-W¹ (-And/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂)) c) W-C)
    (match-define (list c₁ c₂) (-app-split 'and/c c 2))
    (for*/union : (℘ -ς) ([C₂ (in-set (σ@ Σ α₂))]
                         [⟦k⟧* (in-value (mon.c∷ (ctx-with-ℓ ctx ℓ₂) (-W¹ C₂ c₂) ⟦k⟧))]
                         [C₁ (in-set (σ@ Σ α₁))])
      (push-mon (ctx-with-ℓ ctx ℓ₁) (-W¹ C₁ c₁) W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧*)))

  (define (mon-or/c ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo _) ctx)
    (match-define (-W¹ (and C (-Or/C flat? (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))) c) W-C)
    (match-define (list c₁ c₂) (-app-split 'or/c c 2))

    (: chk-or/c : -W¹ -ctx -W¹ -ctx → (℘ -ς))
    (define (chk-or/c W-fl ctx-fl W-ho ctx-ho)
      (match-define (-ctx _ _ lo-fl ℓ-fl) ctx-fl)
      (push-fc lo-fl ℓ-fl W-fl W-V $ Γ ⟪ℋ⟫ Σ
               (mon-or/c∷ ctx-ho W-fl W-ho W-V ⟦k⟧)))

    (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
      (define W-C₁ (-W¹ C₁ c₁))
      (define W-C₂ (-W¹ C₂ c₂))
      (cond [(C-flat? C₁) (chk-or/c W-C₁ (ctx-with-ℓ ctx ℓ₁) W-C₂ (ctx-with-ℓ ctx ℓ₂))]
            [(C-flat? C₂) (chk-or/c W-C₂ (ctx-with-ℓ ctx ℓ₂) W-C₁ (ctx-with-ℓ ctx ℓ₁))]
            [else (error 'or/c "No more than 1 higher-order disjunct for now")])))

  (define (mon-not/c ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ (and C (-Not/C (-⟪α⟫ℓ α ℓ*))) c) W-C)
    (match-define (-W¹ V _) W-V)
    (match-define (list c*) (-app-split 'not/c c 1))
    (define ⟦k⟧*
      (let ([⟦ok⟧ (mk-rt W-V)]
            [⟦er⟧ (mk-rt (-blm l+ lo (list C) (list V) ℓ))])
        (if∷ lo ⟦er⟧ ⟦ok⟧ ⊥ρ ⟦k⟧)))
    (for/union : (℘ -ς) ([C* (σ@ (-Σ-σ Σ) α)])
      (assert C* C-flat?)
      (define W-C* (-W¹ C* c*))
      (app ℓ* W-C* (list W-V) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*)))

  (define (mon-one-of/c ctx Wₚ Wᵥ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ (and C (-One-Of/C bs)) _) Wₚ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (define (blm)
      (⟦k⟧ (-blm l+ lo (list C) (list Vᵥ) ℓ) $ Γ ⟪ℋ⟫ Σ))
    (case (sat-one-of Vᵥ bs)
      [(✓) (⟦k⟧ (-W (list Vᵥ) sᵥ) $ Γ ⟪ℋ⟫ Σ)]
      [(✗) (blm)]
      [(?) (∪ (for/union : (℘ -ς) ([b bs])
                (⟦k⟧ (-W (list (-b b)) sᵥ) $ (Γ+ Γ (?t@ 'equal? sᵥ (-b b))) ⟪ℋ⟫ Σ))
              (blm))]))

  (define (mon-vectorof ctx Wₚ Wᵥ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (match-define (-W¹ (and Vₚ (-Vectorof (-⟪α⟫ℓ α* ℓ*))) _) Wₚ)
    (define σ (-Σ-σ Σ))

    (: blm : -V → → (℘ -ς))
    (define ((blm C))
      (define blm (-blm l+ lo (list C) (list Vᵥ) ℓ))
      (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

    (: chk-elems : → (℘ -ς))
    (define (chk-elems)
      (define Wᵥ* (-W¹ (V+ σ Vᵥ Vₚ) sᵥ))
      (define ⟦ref⟧
        (mk-app ℓ
                (mk-rt (-W¹ 'vector-ref #f))
                (list (mk-rt Wᵥ*)
                      (mk-rt (-W¹ (+● 'exact-nonnegative-integer?) (loc->ℓ (loc 'vof-idx 0 0 '())))))))
      (define ⟦k⟧* (mk-wrap-vect∷ sᵥ Vₚ ctx ⟦k⟧))
      (define c* #f #;(⟪α⟫->s α*))
      (define Wₗ (vec-len σ Γ Wᵥ*))
      (for/union : (℘ -ς) ([C* (in-set (σ@ Σ α*))])
        (define ⟦mon⟧ (mk-mon (ctx-with-ℓ ctx ℓ*) (mk-rt (-W¹ C* c*)) ⟦ref⟧))
        (⟦mon⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (ap∷ (list Wₗ (+W¹ 'make-vector)) '() ⊥ρ ℓ
                                 ⟦k⟧*))))

    (with-Γ⊢oW (σ Γ 'vector? Wᵥ)
      #:on-t chk-elems
      #:on-f (blm 'vector?)))

  (define (mon-vector/c ctx Wₚ Wᵥ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ (and Vₚ (-Vector/C ⟪α⟫ℓs)) sₚ) Wₚ)
    (match-define (-W¹ Vᵥ sᵥ) Wᵥ)
    (define σ (-Σ-σ Σ))
    (define n (length ⟪α⟫ℓs))
    
    (: blm : -V → → (℘ -ς))
    (define ((blm C))
      (define blm (-blm l+ lo (list C) (list Vᵥ) ℓ))
      (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))

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
      (define Wᵥ* (-W¹ (V+ σ Vᵥ Vₚ) sᵥ))

      (for/union : (℘ -ς) ([Cs (in-set (σ@/list σ ⟪α⟫s))])
                 (define ⟦mon-fld⟧s : (Listof -⟦e⟧)
                   (for/list ([Cᵢ (in-list Cs)]
                              [cᵢ (in-list cs)]
                              [ℓᵢ (in-list ℓs)]
                              [i (in-naturals)] #:when (index? i))
                     (define Wᵢ (let ([bᵢ (-b i)]) (-W¹ bᵢ #f)))
                     (define Wₚᵢ (-W¹ Cᵢ cᵢ))
                     (define ⟦ref⟧
                       (mk-app ℓ
                               (mk-rt (-W¹ 'vector-ref #f))
                               (list (mk-rt Wᵥ*) (mk-rt Wᵢ))))
                     (mk-mon (ctx-with-ℓ ctx ℓᵢ) (mk-rt Wₚᵢ) ⟦ref⟧)))
                 
                 (match ⟦mon-fld⟧s
                   ['() (⟦k⟧ (-W (list (-Vector '())) sᵥ) $ Γ ⟪ℋ⟫ Σ)] ; no need to wrap
                   [(cons ⟦fld⟧₀ ⟦fld⟧s)
                    (define ⟦k⟧* (mk-wrap-vect∷ sᵥ Vₚ ctx ⟦k⟧))
                    (⟦fld⟧₀ ⊥ρ $ Γ ⟪ℋ⟫ Σ
                     (ap∷ (list (+W¹ 'vector)) ⟦fld⟧s ⊥ρ ℓ ⟦k⟧*))])))

    (with-Γ⊢oW (σ Γ 'vector? Wᵥ)
      #:on-t chk-len
      #:on-f (blm 'vector?)))

  (define (mon-hash/c ctx Wₚ Wᵤ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ (and Vₚ (-Hash/C (-⟪α⟫ℓ αₖ ℓₖ) (-⟪α⟫ℓ αᵥ ℓᵥ))) sₚ) Wₚ)
    (match-define (-W¹ Vᵤ tᵤ) Wᵤ)
    (define σ (-Σ-σ Σ))

    (: chk-content : → (℘ -ς))
    (define (chk-content)
      (define αₕ (-α->⟪α⟫ (-α.unhsh ctx ⟪ℋ⟫)))
      
      (: chk-key-vals : (℘ -V) (℘ -V) → (℘ -ς))
      (define (chk-key-vals Vsₖ Vsᵥ)
        (define wrap (mk-wrapped-hash Vₚ ctx αₕ (-W¹ (V+ σ Vᵤ 'hash?) tᵤ)))
        (cond ;; FIXME hacks for now
          [(or (set-empty? Vsₖ) (set-empty? Vsᵥ))
           (wrap ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
          [else
           (define doms (σ@ Σ αₖ))
           (define rngs (σ@ Σ αᵥ))
           (for*/union : (℘ -ς) ([Cᵥ (in-set rngs)] [Vᵥ (in-set Vsᵥ)])
             (define mon-vals (mk-mon (ctx-with-ℓ ctx ℓᵥ) (mk-rt (-W¹ Cᵥ #|TODO|# #f)) (mk-rt (-W¹ Vᵥ #|TODO|# #f))))
             (define ⟦k⟧* (bgn∷ (list mon-vals wrap) ⊥ρ ⟦k⟧))
             (for*/union : (℘ -ς) ([Cₖ (in-set doms)] [Vₖ (in-set Vsₖ)])
               (push-mon (ctx-with-ℓ ctx ℓₖ) (-W¹ Cₖ #|TODO|# #f) (-W¹ Vₖ #|TODO|# #f) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*)))]))
      
      (match Vᵤ
        [(? -Hash/guard?)
         ;; havoc would be expensive. Just wrap it for now
         (σ⊕V! Σ αₕ Vᵤ)
         (define V (-Hash/guard Vₚ αₕ ctx))
         (⟦k⟧ (-W (list V) tᵤ) $ Γ ⟪ℋ⟫ Σ)]
        [(-Hash^ α₁ α₂ _)
         (chk-key-vals (σ@ Σ α₁) (σ@ Σ α₂))]
        {_
         (define ●s {set (+●)})
         (chk-key-vals ●s ●s)}))

    (with-Γ⊢oW (σ Γ 'hash? Wᵤ)
      #:on-t chk-content
      #:on-f (λ ()
               (define blm (-blm l+ lo '(hash?) (list Vᵤ) ℓ))
               (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))))

  (define (mon-set/c ctx Wₚ Wᵤ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ (and Vₚ (-Set/C (-⟪α⟫ℓ αₑ ℓₑ))) sₚ) Wₚ)
    (match-define (-W¹ Vᵤ tᵤ) Wᵤ)
    (define σ (-Σ-σ Σ))

    (: chk-content : → (℘ -ς))
    (define (chk-content)
      (define αₛ (-α->⟪α⟫ (-α.unset ctx ⟪ℋ⟫)))

      (: chk-elems : (℘ -V) → (℘ -ς))
      (define (chk-elems Vs)
        (define wrap (mk-wrapped-set Vₚ ctx αₛ (-W¹ (V+ σ Vᵤ 'set?) tᵤ)))
        (cond
          [(set-empty? Vs)
           (wrap ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
          [else
           (define ⟦k⟧* (bgn∷ (list wrap) ⊥ρ ⟦k⟧))
           (for*/union : (℘ -ς) ([C (in-set (σ@ σ αₑ))] [V (in-set Vs)])
             (push-mon (ctx-with-ℓ ctx ℓₑ) (-W¹ C #|TODO|# #f) (-W¹ V #|TODO|# #f) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*))]))

      (match Vᵤ
        [(? -Set/guard?)
         (σ⊕V! Σ αₛ Vᵤ)
         (define V (-Set/guard Vₚ αₛ ctx))
         (⟦k⟧ (-W (list V) tᵤ) $ Γ ⟪ℋ⟫ Σ)]
        [(-Set^ α _) (chk-elems (σ@ σ α))]
        [_ (chk-elems {set (+●)})]))

    (with-Γ⊢oW (σ Γ 'set? Wᵤ)
      #:on-t chk-content
      #:on-f (λ ()
               (define blm (-blm l+ lo '(set?) (list Vᵤ) ℓ))
               (⟦k⟧ blm $ Γ ⟪ℋ⟫ Σ))))

  (define (mon-seal/c ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-W¹ (and C (-Seal/C x ⟪ℋ⟫ l)) _) W-C)
    (match-define (-W¹ V tᵥ) W-V)
    (match-define (-ctx l+ l- lo ℓ) ctx)
    (define α (-α->⟪α⟫ (-α.sealed x ⟪ℋ⟫)))
    (cond
      [(equal? l l+) ; seal
       (σ⊕! Σ Γ α W-V)
       (⟦k⟧ (-W (list (-Sealed α)) tᵥ) $ Γ ⟪ℋ⟫ Σ)]
      [(equal? l l-) ; unseal
       (define (blm) (⟦k⟧ (-blm l+ lo (list C) (list V) ℓ) $ Γ ⟪ℋ⟫ Σ))
       (define (ok)
         (for/union : (℘ -ς) ([V* (in-set (σ@ Σ α))])
           (⟦k⟧ (-W (list V*) tᵥ) $ Γ ⟪ℋ⟫ Σ)))
       (match V
         [(-Sealed (== α)) (ok)] ; TODO possible false negs from finite seals
         [(-● _) (∪ (blm) (ok))]
         [_ (blm)])]
      [else
       (error 'mon-seal/c "seal labeled ~a in context ~a, ~a, ~a" l l+ l- lo)]))
  
  (define (mon-flat/c ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (match-define (-ctx l+ _ lo ℓ) ctx)
    (match-define (-W¹ C c) W-C)
    (match-define (-W¹ V v) W-V)
    (define cv (and (-h? c) (?t@ c v)))
    (case (Γ⊢V∈C (-Σ-σ Σ) Γ W-V W-C)
      [(✓) (⟦k⟧ (-W (list V) v) $ Γ ⟪ℋ⟫ Σ)]
      [(✗) (⟦k⟧ (-blm l+ lo (list C) (list V) ℓ) $ Γ ⟪ℋ⟫ Σ)]
      [(?)
       (define V* (V+ (-Σ-σ Σ) V C))
       (define ⟦k⟧* (if.flat/c∷ (-W (list V*) v) (-blm l+ lo (list C) (list V) ℓ) ⟦k⟧))
       (match C
         [(? -b? b)
          (app ℓ (-W¹ 'equal? 'equal?) (list W-V (-W¹ b b)) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*)]
         [_
          (app ℓ W-C (list W-V) $ Γ ⟪ℋ⟫ Σ ⟦k⟧*)])]))

  (: flat-chk : -l ℓ -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς))
  (define (flat-chk l ℓₐ W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧)
    (define σ (-Σ-σ Σ))
    (match-define (-W¹ C c) W-C)
    (match-define (-W¹ V v) W-V)
    (match C
      [(-And/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (match-define (list c₁ c₂) (-app-split 'and/c c 2))
       (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
         (define W-C₁ (-W¹ C₁ c₁))
         (define W-C₂ (-W¹ C₂ c₂))
         (push-fc l ℓ₁ W-C₁ W-V $ Γ ⟪ℋ⟫ Σ
                  (fc-and/c∷ l ℓ₂ W-C₁ W-C₂ ⟦k⟧)))]
      [(-Or/C _ (-⟪α⟫ℓ α₁ ℓ₁) (-⟪α⟫ℓ α₂ ℓ₂))
       (match-define (list c₁ c₂) (-app-split 'or/c c 2))
       (for*/union : (℘ -ς) ([C₁ (σ@ Σ α₁)] [C₂ (σ@ Σ α₂)])
         (define W-C₁ (-W¹ C₁ c₁))
         (define W-C₂ (-W¹ C₂ c₁))
         (push-fc l ℓ₁ W-C₁ W-V $ Γ ⟪ℋ⟫ Σ
                  (fc-or/c∷ l ℓ₂ W-C₁ W-C₂ W-V ⟦k⟧)))]
      [(-Not/C (-⟪α⟫ℓ α ℓ*))
       (match-define (list c*) (-app-split 'not/c c 1))
       (for/union : (℘ -ς) ([C* (σ@ Σ α)])
         (define W-C* (-W¹ C* c*))
         (push-fc l ℓ* W-C* W-V $ Γ ⟪ℋ⟫ Σ
                  (fc-not/c∷ l W-C* W-V ⟦k⟧)))]
      [(-One-Of/C bs)
       (case (sat-one-of V bs)
         [(✓) (⟦k⟧ (-W (list -tt V) (?t@ 'values -tt v)) $ Γ ⟪ℋ⟫ Σ)]
         [(✗) (⟦k⟧ (+W (list -ff)) $ Γ ⟪ℋ⟫ Σ)]
         [(?)
          (∪
           (for/union : (℘ -ς) ([b bs])
                      (define v (-b b))
                      (⟦k⟧ (-W (list -tt v) (?t@ 'values -tt v)) $ Γ ⟪ℋ⟫ Σ))
           (⟦k⟧ (+W (list -ff)) $ Γ ⟪ℋ⟫ Σ))])]
      [(-St/C _ s αℓs)

       (: chk-fields : → (℘ -ς))
       (define (chk-fields)
         (define-values (αs ℓs) (unzip-by -⟪α⟫ℓ-addr -⟪α⟫ℓ-loc αℓs))
         (define cs (-struct/c-split c s))
         (for/union : (℘ -ς) ([Cs (σ@/list σ αs)])
           (define ⟦chk-field⟧s : (Listof -⟦e⟧)
             (let ([W-V* (-W¹ (V+ σ V (-st-p s)) v)])
               (for/list ([Cᵢ (in-list Cs)]
                          [cᵢ (in-list cs)]
                          [ℓᵢ : ℓ (in-list ℓs)]
                          [i (in-naturals)] #:when (index? i))
                 (define ac (-st-ac s i))
                 (define ⟦ref⟧ᵢ (mk-app ℓₐ (mk-rt (-W¹ ac ac)) (list (mk-rt W-V*))))
                 (mk-fc l ℓᵢ (mk-rt (-W¹ Cᵢ cᵢ)) ⟦ref⟧ᵢ))))
           (match ⟦chk-field⟧s
             ['()
              (define p (-st-p s))
              (define ⟦rt⟧ (mk-rt (-W (list -tt (V+ σ V p)) (?t@ 'values -tt v))))
              (⟦rt⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)]
             [(cons ⟦chk-field⟧ ⟦chk-field⟧s*)
              (⟦chk-field⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ
               (fc-struct/c∷ l ℓₐ s '() ⟦chk-field⟧s* ⊥ρ ⟦k⟧))])))

       (with-Γ⊢oW (σ Γ (-st-p s) W-V)
         #:on-t chk-fields
         #:on-f (λ () ((↓ₚᵣₘ -ff) ⊥ρ $ Γ ⟪ℋ⟫ Σ ⟦k⟧)))]
      [(-x/C ⟪α⟫)
       (define αₓ (cast (⟪α⟫->-α ⟪α⟫) -α.rec-ref))
       (for/union : (℘ -ς) ([C* (σ@ Σ ⟪α⟫)])
                  (push-fc l ℓₐ (-W¹ C* #f) W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧ #:looped αₓ))]
      [(? -b? b)
       (define ⟦ap⟧ (mk-app ℓₐ (mk-rt (-W¹ 'equal? 'equal?)) (list (mk-rt W-V) (mk-rt (-W¹ b b)))))
       (define ⟦rt⟧ (mk-rt (-W (list -tt b) (?t@ 'values -tt b))))
       (⟦ap⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ (↓ₚᵣₘ -ff) ⊥ρ ⟦k⟧))]
      [_
       (define ⟦ap⟧ (mk-app ℓₐ (mk-rt W-C) (list (mk-rt W-V))))
       (define ⟦rt⟧ (mk-rt (-W (list -tt (V+ σ V C)) (?t@ 'values -tt v))))
       (⟦ap⟧ ⊥ρ $ Γ ⟪ℋ⟫ Σ (if∷ l ⟦rt⟧ (↓ₚᵣₘ -ff) ⊥ρ ⟦k⟧))]))

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

  (: push-mon ((-ctx -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧) (#:looped (Option -α.rec-ref)) . ->* . (℘ -ς)))
  (define (push-mon ctx W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧ #:looped [?αₓ #f])
    (match-define (-ctx _ _ _ ℓ) ctx)
    (match-define (-W¹ C _ ) W-C)
    (match-define (-W¹ V tᵥ) W-V)
    (define-values (⟪ℋ⟫ₑₑ _) (⟪ℋ⟫+ ⟪ℋ⟫ (-edge (strip-C C) ℓ)))
    (define ⟦k⟧* (restore-ctx∷ ⟪ℋ⟫ ⟦k⟧))
    (match ?αₓ
      [(or (-α.x/c x _) (-α.imm-listof x _))
       #:when x
       (define W-V* (-W¹ V (-t.x x)))
       (define $* ($-set $ x (-t.x x)))
       (define Γ* #|TODO|# ⊤Γ)
       (define $**
         (let ([root (∪ (V->⟪α⟫s V) (V->⟪α⟫s C) (⟦k⟧->⟪α⟫s ⟦k⟧ (-Σ-σₖ Σ)))])
           ($-cleanup (gc-$ $* (-Σ-σ Σ) root))))
       (define αₖ (-ℳ $** ⟪ℋ⟫ₑₑ ctx W-C W-V* Γ*))
       (define κ
         (let* ([δ$ : -δ$ (hash x (cond [(hash-ref $ x #f) => values] [else #f]))]
                [⟦k⟧** (restore-$∷ δ$ ⟦k⟧*)])
           (-κ.rt ⟦k⟧** ($-symbolic-names $) Γ tᵥ #t)))
       (σₖ⊕! Σ αₖ κ)
       {set (-ς↑ αₖ)}]
      [_
       (mon ctx W-C W-V $ Γ ⟪ℋ⟫ₑₑ Σ ⟦k⟧*)]))

  (: push-fc ((-l ℓ -W¹ -W¹ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧) (#:looped (Option -α.rec-ref)) . ->* . (℘ -ς)))
  (define (push-fc l ℓ W-C W-V $ Γ ⟪ℋ⟫ Σ ⟦k⟧ #:looped [?αₓ #f])
    (match-define (-W¹ C _ ) W-C)
    (match-define (-W¹ V tᵥ) W-V)
    (define-values (⟪ℋ⟫ₑₑ _) (⟪ℋ⟫+ ⟪ℋ⟫ (-edge (strip-C C) ℓ)))
    (define ⟦k⟧* (restore-ctx∷ ⟪ℋ⟫ ⟦k⟧))
    (match ?αₓ
      [(or (-α.x/c x _) (-α.imm-listof x _))
       #:when x
       (define W-V* (-W¹ V (-t.x x)))
       (define $* ($-set $ x (-t.x x)))
       (define $**
         (let ([root (∪ (V->⟪α⟫s V) (V->⟪α⟫s C) (⟦k⟧->⟪α⟫s ⟦k⟧ (-Σ-σₖ Σ)))])
           ($-cleanup (gc-$ $* (-Σ-σ Σ) root))))
       (define Γ* #|TODO|# ⊤Γ)
       (define κ
         (let* ([δ$ : -δ$ (hash x (cond [(hash-ref $ x #f) => values] [else #f]))]
                [⟦k⟧** (restore-$∷ δ$ ⟦k⟧*)])
           (-κ.rt ⟦k⟧** ($-symbolic-names $) Γ tᵥ #t)))
       (define αₖ (-ℱ $** ⟪ℋ⟫ₑₑ l ℓ W-C W-V* Γ*))
       (σₖ⊕! Σ αₖ κ)
       {set (-ς↑ αₖ)}]
      [_
       (flat-chk l ℓ W-C W-V $ Γ ⟪ℋ⟫ₑₑ Σ ⟦k⟧*)]))

  ;; FIXME Duplicate macros
  (define-simple-macro (with-Γ+/-oW (σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
    (Γ+/-oW/handler on-t on-f σ Γ o W ...))
  (define-simple-macro (with-Γ⊢oW (σ:expr Γ:expr o:expr W:expr ...) #:on-t on-t:expr #:on-f on-f:expr)
    (Γ⊢oW/handler on-t on-f σ Γ o W ...))
  )
