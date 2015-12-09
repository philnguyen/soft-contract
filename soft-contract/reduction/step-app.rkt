#lang typed/racket/base

(require
 racket/match racket/set racket/function
 "../utils/list.rkt" "../utils/debug.rkt" "../utils/map.rkt" "../utils/non-det.rkt" "../utils/set.rkt"
 "../utils/untyped-macros.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/val.rkt" "../runtime/simp.rkt" "../runtime/env.rkt" "../runtime/store.rkt"
 "../runtime/addr.rkt" "../runtime/path-inv.rkt" "../runtime/arity.rkt" "../runtime/summ.rkt"
 "../delta.rkt"
 "../machine/definition.rkt" "../machine/havoc.rkt"
 "../proof-relation/main.rkt"
 "step-mon.rkt")

(provide ↦@ rt-spurious?)

(: ↦@ : -WV (Listof -WV) -Γ -κ -σ -Ξ -M -src-loc → -Δς*)
;; Stepping rules for function application
(define (↦@ W_f W_xs Γ κ σ Ξ M loc)

  (match-define (-src-loc l pos) loc)

  (match-define (-W V_f e_f) W_f)
  (define-values (V_xs e_xs) ((inst unzip-by -WV -V -?e) -W-x -W-e W_xs))
  (define e_a (apply -?@ e_f e_xs))

  (dbg '↦@ "App:~n f: ~a~n xs: ~a~n" (show-V V_f) (map show-V V_xs))

  (define-syntax-rule (with-guarded-arity e ...)
    (let ([n (length W_xs)]
          [a (-procedure-arity V_f)])
      (cond
        [a =>
         (λ (a)
           (cond
             [(-arity-includes? a n) e ...]
             [else (-Δς (-blm l 'Λ (-Arity-Includes/C n) (list V_f)) Γ κ '() '() '())]))]
        [else
         (unless (-●? V_f)
           (printf "Warning: no arity for ~a~n" (show-V V_f)))
         (define ans (begin e ...))
         (cond [(set? ans) (set-add ans (-Δς (-W (list -●/V) #f) Γ κ '() '() '()))]
               [else {set ans (-Δς (-W (list -●/V) #f) Γ κ '() '() '())}])])))

  (: ↦β : -formals -e -ρ -Γ → -Δς*)
  (define (↦β xs e ρ_f Γ_f)
    (match xs
      [(? list? xs)
       (define-values (ρ* σ* δσ)
         (for/fold ([ρ* : -ρ ρ_f] [σ* : -σ σ] [δσ : -Δσ '()])
                   ([x xs] [V_x V_xs] [ex e_xs])
           (define α x #;(-α.bnd x ex (if ex (Γ↓ Γ (FV ex)) -Γ⊤)))
           (define V_x* (close-Γ Γ V_x))
           (values (ρ+ ρ* x α)
                   (⊔ σ* α V_x*)
                   (cons (cons α V_x*) δσ))))
       (define τ (-τ e ρ* Γ_f))
       (define κ* (-kont (-φ.rt.@ Γ xs e_f e_xs) κ))
       (define δΞ (list (cons τ κ*)))
       ;(define Ξ* (⊔ Ξ τ κ*))
       (-Δς (-⇓ e ρ*) Γ_f τ δσ δΞ '())]
      [(-varargs zs z) (error '↦@ "TODO: varargs")]))

  (: ↦δ : Symbol → -Δς*)
  (define (↦δ o)
    (define-values (δσ AΓ) (δ M σ Γ o W_xs loc))
    (match/nd: (-AΓ → -Δς) AΓ
      [(-AΓ (? -blm? blm) Γ*) (-Δς blm         Γ* κ δσ '() '())]
      [(-AΓ (? list? Vs ) Γ*) (-Δς (-W Vs e_a) Γ* κ δσ '() '())]))
  
  (: ↦havoc : → (Setof -Δς))
  (define (↦havoc)
    (define V_havoc (σ@₁ σ (-α.def -havoc-id)))
    (define W_havoc (-W V_havoc (-ref -havoc-id l 0)))
    (for/fold ([acc : (Setof -Δς) ∅]) ([W_x W_xs])
      (match (↦@ W_havoc (list W_x) Γ κ σ Ξ M -Λ)
        [(? set? s) (∪ acc s)]
        [(? -Δς? ς) (set-add acc ς)])))

  (: ↦opq : → -Δς)
  (define (↦opq) (-Δς (-W -●/Vs e_a) Γ κ '() '() '()))

  (: ↦indy : (Listof Symbol) (Listof -?e) (Listof -V) -e -ρ -Γ -V Mon-Info → -Δς*)
  (define (↦indy xs cs Cs d ρ_d Γ_d V_g l³)
    ;; TODO: probably don't need these restoring frames anymore. Check again.
    (define κ₁ (-kont (-φ.rt.@ Γ xs e_f e_xs) κ))
    (match* (xs cs Cs W_xs)
      [('() '() '() '())
       ;; If there's no argument, skip monitoring arguments and start evaluating range
       (define κ₂ (-kont (-φ.indy.rng V_g '() l³ pos) κ₁))
       (-Δς (-⇓ d ρ_d) Γ_d κ₂ '() '() '())]
      [((cons x xs*) (cons c cs*) (cons C Cs*) (cons W_x W_xs*))
       (define l³* (swap-parties l³))
       (define W_c (-W C c))
       (define W_x* (-W (-W-x W_x) (-x x)))
       (define κ₂ (-kont (-φ.indy.dom x xs* cs* Cs* W_xs* '() V_g d ρ_d l³ pos) κ₁))
       (↦mon W_c W_x* Γ_d κ₂ σ Ξ M l³* pos)]))

  (: ↦pred : -struct-info → -Δς)
  (define (↦pred si)
    (case (MσΓ⊢oW M σ Γ (-st-p si) (car W_xs))
      [(✓) (-Δς (-W (list -tt) e_a) (Γ+ Γ e_a) κ '() '() '())]
      [(X) (-Δς (-W (list -ff) e_a) (Γ+ Γ (-not e_a)) κ '() '() '())]
      [(?) (-Δς (-W -●/Vs e_a) Γ κ '() '() '())]))

  (: ↦con : -struct-info → -Δς)
  (define (↦con si)
    (define αs (alloc-fields si pos))
    (define δσ : -Δσ
      (for/list ([α αs] [W W_xs])
        (cons α (close-Γ Γ (-W-x W)))))
    (-Δς (-W (list (-St si αs)) e_a) Γ κ δσ '() '()))

  (: ↦ac : -struct-info Integer → -Δς*)
  (define (↦ac si i)
    (match-define (-struct-info id n _) si)
    (match-define (list (and W (-W V e))) W_xs)
    (match V
      [(-St (≡ si) αs)
       (for/set: : (Setof -Δς) ([V (σ@ σ (list-ref αs i))])
         (-Δς (-W (list V) e_a) Γ κ '() '() '()))]
      [(-St/checked (≡ si) γs l³ α)
       (define o (-st-ac si i))
       (define φ-select (-φ.@ '() (list (-W o o)) -Λ))
       (define e_x (car e_xs))
       (cond
         [(list-ref γs i) =>
          (λ ([γ : -α])
            (for/set: : (Setof -Δς) ([C* (σ@ σ γ)] [V* (σ@ σ α)])
              (define φ-mon (-φ.mon.v (-W C* #f) l³ pos))
              (define κ* (-kont* φ-select φ-mon κ))
              (-Δς (-W (list V*) e_x) Γ κ* '() '() '())))]
         [else
          (define κ* (-kont φ-select κ))
          (for/set: : (Setof -Δς) ([V* (σ@ σ α)])
            (-Δς (-W (list V*) e_x) Γ κ* '() '() '()))])]
      [(-●) (-Δς (-W -●/Vs e_a) Γ κ '() '() '())]
      [_ ∅]))

  (: ↦mut : -struct-info Integer → -Δς*)
  (define (↦mut si i)
    (match-define (list (and W₁ (-W V₁ e₁)) (-W V₂ e₂)) W_xs)
    (match V₁
      [(-St _ αs)
       (define δσ (list (cons (list-ref αs i) V₂)))
       (-Δς -Void/W Γ κ δσ '() '())]
      [(-St/checked s γs (and l³ (list l+ l- lo)) α)
       (define e_x (car e_xs))
       (define o (-st-mut si i))
       (cond
         [(list-ref γs i) =>
          (λ ([γ : -α])
            (define l³* (list l- l+ lo))
            (for/set: : (Setof -Δς) ([C* (σ@ σ γ)] [V* (σ@ σ α)])
              (define φ-mon (-φ.mon.v (-W C* #f) l³* pos))
              (define φ-mut
                (-φ.@ '() (list (-W o o) (-W V* e₁)) (-src-loc lo pos)))
              (define κ* (-kont* φ-mon φ-mut κ))
              (-Δς (-W (list V₂) e₂) Γ κ* '() '() '())))]
         [else
          (for/set: : (Setof -Δς) ([V* (σ@ σ α)])
            (define φ-mut
              (-φ.@ '() (list (-W o o) (-W V* e₁)) (-src-loc lo pos)))
            (define κ* (-kont φ-mut κ))
            (-Δς (-W (list V*) e_x) Γ κ* '() '() '()))])]
      [_
       ;; TODO: unsound if V₂ concrete buggy higher-order and V₁ opaque
       (-Δς -Void/W Γ κ '() '() '())]))

  (: with-vector-bound-check : -M -σ -Γ -WV -WV (-Γ → -Δς*) → -Δς*)
  (define (with-vector-bound-check M σ Γ W-vec W-idx mk-ok)
    (match-define (-W V-vec e-vec) W-vec)
    (match-define (-W V-idx _    ) W-idx)
    (define e-len (-?@ 'vector-length e-vec))
    (define V-len
      (match V-vec
        [(-Vector αs) (-b (length αs))]
        [_ -●/V]))
    (define W-len (-W V-len e-len))
    (define ((blm [p : -V] [V : -V]) [Γ : -Γ]) : -Δς
      (-Δς (-blm l 'vector-ref p (list V)) Γ κ '() '() '()))
    (define-values (ans-ok ans-bads)
      (Γ+/- M σ Γ mk-ok
            (list -vector?/W (list W-vec) (blm 'vector? V-vec))
            (list -integer?/W (list W-idx) (blm 'integer? V-idx))
            (list (-W '>= '>=) (list W-idx (-W (-b 0) (-b 0)))
                  (blm (-Clo '(x) (-@ '>= (list (-x 'x) (-b 0)) -Λ) -ρ⊥ -Γ⊤) V-idx))
            (list (-W '< '<) (list W-idx W-len)
                  (blm (-Clo '(x) (-@ '< (list (-x 'x) (or e-len #|HACK|# (-x 'len))) -Λ) -ρ⊥ -Γ⊤) V-idx))))
    (collect ans-ok ans-bads))

  (: ↦vector-ref : → -Δς*)
  (define (↦vector-ref)
    (match-define (list (and W-vec (-W V-vec e-vec)) (and W-idx (-W V-idx e-idx))) W_xs)
    (with-vector-bound-check M σ Γ W-vec W-idx
      (λ ([Γ-ok : -Γ]) : -Δς*
         (match V-vec
           [(-Vector αs)
            (match V-idx
              [(-b (? exact-integer? i))
               (for/set: : (Setof -Δς) ([V (σ@ σ (list-ref αs i))])
                 (-Δς (-W (list V) e_a) Γ-ok κ '() '() '()))]
              [_
               ;; If index opaque, return everything in addition to refining index
               ;; FIXME ouch. This explodes fast.
               (for/fold ([acc : (Setof -Δς) ∅]) ([(α i) (in-indexed αs)])
                 (define ψ (-?@ '= e-idx (-b i)))
                 (match (MσΓ⊢e M σ Γ-ok ψ)
                   ['X acc]
                   [_
                    (define Γ* (Γ+ Γ-ok ψ))
                    (for/fold ([acc : (Setof -Δς) acc]) ([V (σ@ σ α)])
                      (set-add acc (-Δς (-W (list V) e_a) Γ* κ '() '() '())))]))])]
           [(-Vector/checked γs l³ α)
            (for/fold ([acc : (Setof -Δς) ∅]) ([V (σ@ σ α)])
              (for/fold ([acc : (Setof -Δς) acc]) ([(γ i) (in-indexed γs)])
                (define ψ (-?@ '= e-idx (-b i)))
                (match (MσΓ⊢e M σ Γ-ok ψ)
                  ['X acc]
                  [_
                   (define Γ* (Γ+ Γ-ok ψ))
                   (for/fold ([acc : (Setof -Δς) acc]) ([C (σ@ σ γ)])
                     (define φ₁ (-φ.mon.v (-W C #f #|TODO|#) l³ pos))
                     (define φ₂
                       (-φ.@ (list (-W (list V-idx) e-idx)) (list -vector-ref/W) -Λ))
                     (define κ* (-kont* φ₂ φ₁ κ))
                     (set-add acc (-Δς (-W (list V) e-vec) Γ* κ* '() '() '())))])))]
           [_ (-Δς (-W -●/Vs e_a) Γ-ok κ '() '() '())]))))

  (: ↦vector-set! : → -Δς*)
  (define (↦vector-set!)
    (match-define (list (and W-vec (-W V-vec e-vec))
                        (and W-idx (-W V-idx _))
                        (-W V-val e-val))
      W_xs)
    (with-vector-bound-check M σ Γ W-vec W-idx
      (λ ([Γ-ok : -Γ]) : -Δς*
         (match V-vec
           [(-Vector αs)
            (define δσ
              (match V-idx
                [(-b (? exact-integer? i))
                 (list (cons (list-ref αs i) V-val))]
                [_ ;; FIXME ouch. This explodes
                 (for/list : -Δσ ([α αs])
                   (cons α V-val))]))
            (-Δς -Void/W Γ-ok κ δσ '() '())]
           [(-Vector/checked γs l³ α)
            (define Cs
              (match V-idx
                [(-b (? exact-integer? i)) (σ@ σ (list-ref γs i))]
                [_ ; FIXME this explodes fast
                 (for/union : (Setof -V) ([γ γs])
                            (σ@ σ γ))]))
            (define Vs (σ@ σ α))
            (for/set: : (Setof -Δς) ([C Cs] [V Vs])
              (define φ₁ (-φ.@ '() (list W-idx (-W V e-vec) -vector-set/W) -Λ))
              (define φ₂ (-φ.mon.v (-W C #f #|TODO|#) l³ pos))
              (define κ* (-kont* φ₂ φ₁ κ))
              (-Δς (-W (list V-val) e-val) Γ-ok κ* '() '() '()))]
           [_
            (-Δς -Void/W Γ-ok κ '() '() '())]))))

  (: ↦and/c : (Setof -V) (Setof -V) → -Δς*)
  (define (↦and/c Cs Ds)
    (match-define (list (and W_x (-W V_x e_x))) W_xs)
    (match-define (list e_c e_d) (-app-split e_f 'and/c 2))
    (for*/fold ([acc : (Setof -Δς) ∅])
               ([C Cs]
                [W_C (in-value (-W C e_c))]
                [φ.C (in-value (-φ.@ '() (list W_C) loc))]
                [D Ds])
      (define φ.D (-φ.if (-App (-W D e_d) (list W_x) loc) (-W (list -ff) -ff)))
      (set-add acc (-Δς (-W (list V_x) e_x) Γ (-kont* φ.C φ.D κ) '() '() '()))))

  (: ↦or/c : (Setof -V) (Setof -V) → -Δς*)
  (define (↦or/c Cs Ds)
    (match-define (list (and W_x (-W V_x e_x))) W_xs)
    (match-define (list e_c e_d) (-app-split e_f 'or/c 2))
    (for*/fold ([acc : (Setof -Δς) ∅])
               ([C Cs]
                [W_C (in-value (-W C e_c))]
                [φ.C (in-value (-φ.@ '() (list W_C) loc))]
                [D Ds])
      (define φ.D (-φ.if (-W (list -tt) -tt) #|FIXME sloppy|#
                         (-App (-W D e_d) (list W_x) loc)))
      (set-add acc (-Δς (-W (list V_x) e_x) Γ (-kont* φ.C φ.D κ) '() '() '()))))

  (: ↦not/c : (Setof -V) → -Δς*)
  (define (↦not/c Cs)
    (match-define (list (-W V_x e_x)) W_xs)
    (define φ-not (-φ.@ '() (list (-W 'not 'not)) loc))
    (match-define (list e*) (-app-split e_f 'not/c 1))
    (for/set: : (Setof -Δς) ([C Cs])
      (define φ (-φ.@ '() (list (-W C e*)) loc))
      (-Δς (-W (list V_x) e_x) Γ (-kont* φ φ-not κ) '() '() '())))
  
  (: ↦contract-first-order-passes? : → -Δς*)
  (define (↦contract-first-order-passes?)
    (match-define (list (and W_C (-W C e_c)) (and W_V (-W V e_v))) W_xs)
    (match-define (list c₁ c₂) (-app-split e_c 'and/c 2))
    (match C
      [(-And/C _ α₁ α₂)
       (for*/set: : (Setof -Δς)
                  ([C₁ (σ@ σ α₁)]
                   [φ₁ (in-value (-φ.@ '() (list -contract-first-order-passes?/W (-W C₁ c₁)) loc))]
                   [C₂ (σ@ σ α₂)])
         (define κ*
           (-kont* φ₁
                   (-φ.if (-App -contract-first-order-passes?/W (list (-W C₂ c₂) W_V) loc)
                          (-W (list -ff) -ff))
                   κ))
         (-Δς (-W (list V) e_v) Γ κ* '() '() '()))]
      [(-Or/C flat? α₁ α₂)
       (for*/set: : (Setof -Δς)
                  ([C₁ (σ@ σ α₁)]
                   [φ₁ (in-value (-φ.@ '() (list -contract-first-order-passes?/W (-W C₁ c₁)) loc))]
                   [C₂ (σ@ σ α₂)])
         (define κ*
           (-kont* φ₁
                   (-φ.if (-W (list -tt) -tt)
                          (-App -contract-first-order-passes?/W
                                (list (-W C₂ c₂) W_V)
                                loc))
                   κ))
         (-Δς (-W (list V) e_v) Γ κ* '() '() '()))]
      [(-Not/C α)
       (↦@ W_C (list W_V) Γ κ σ Ξ M loc)]
      [(-St/C flat? si γs)
       (case (MσΓ⊢oW M σ Γ (-st-p si) W_V)
         [(✓)
          (define n (length γs))
          (define cs (-struct/c-split e_c n))
          (define vs (-app-split e_v (-st-mk si) n))
          (define cvs : (Listof (Pairof -?e -?e)) (map (inst cons -?e -?e) cs vs))
          (match V
            [(-St _ #|≡ si|# αs)
             ;; TODO: this explodes like crazy...
             (match* (γs αs)
               [('() '())
                (-Δς (-W (list -tt) -tt) Γ κ '() '() '())]
               [((cons γ γs*) (cons α αs*))
                (match-define (cons (cons c₀ v₀) cvs*) cvs)
                (for*/set: : (Setof -Δς)
                           ([C₀ (in-set (σ@ σ γ))]
                            [V₀ (in-set (σ@ σ α))]
                            [E₀ (in-value (-W (list V₀) v₀))]
                            [φ₀ (in-value
                                 (-φ.@ '()
                                       (list -contract-first-order-passes?/W (-W C₀ c₀))
                                       loc))]
                            [Cs* (in-set (σ@/list σ γs*))]
                            [Vs* (in-set (σ@/list σ αs*))])
                  (define κ*
                    (foldr
                     (λ ([Ci : -V] [Vi : -V] [cvi : (Pairof -?e -?e)] [κ : -κ])
                       (-kont (-φ.if (-App -contract-first-order-passes?/W
                                           (list (-W Ci (car cvi)) (-W Vi (cdr cvi)))
                                           loc)
                                     (-W (list -ff) -ff))
                              κ))
                     κ
                     Cs*
                     Vs*
                     cvs*))
                  (-Δς E₀ Γ (-kont φ₀ κ*) '() '() '()))])]
            [_ (-Δς (-W -●/Vs (-?@ (-st-p si) e_v)) Γ κ '() '() '())])]
         [(X) (-Δς (-W (list -ff) (-?@ (-st-p si) e_v)) Γ κ '() '() '())]
         [else (-Δς (-W -●/Vs (-?@ (-st-p si) e_v)) Γ κ '() '() '())])]
      [(-=>i xs _ _ rst _ _ _) ; check arity
       (cond
         [(-procedure-arity V)
          =>
          (λ ([ar : -Arity])
            (define ans
              (cond
                [(-arity-includes? ar (if rst (-Arity-At-Least (length xs)) (length xs)))
                 (-W (list -tt) -tt)]
                [else (-W (list -ff) -ff)]))
            (-Δς ans Γ κ '() '() '()))]
         [else
          (-Δς (-W -●/Vs (-?@ 'contract-first-order-passes e_c e_v)) Γ κ '() '() '())])]
      [(or (? -Clo?) (? -Clo*?) (? -o?) (? -Ar?))
       (↦@ W_C (list W_V) Γ κ σ Ξ M loc)]))

  (match V_f
    [(-st-p si) (↦pred si)]
    [(-st-mk si) (↦con si)]
    [(-st-ac si i) (↦ac si i)]
    [(-st-mut si i) (↦mut si i)]
    ['vector-ref (↦vector-ref)]
    ['vector-set! (↦vector-set!)]
    ['contract-first-order-passes? (↦contract-first-order-passes?)]
    [(-And/C #t α₁ α₂) (with-guarded-arity (↦and/c (σ@ σ α₁) (σ@ σ α₂)))]
    [(-Or/C  #t α₁ α₂) (with-guarded-arity (↦or/c (σ@ σ α₁) (σ@ σ α₂)))]
    [(-Not/C α) (with-guarded-arity (↦not/c (σ@ σ α)))]
    [(? symbol? o) (↦δ o)]
    [(-Clo* xs e ρ_f    ) (with-guarded-arity (↦β xs e ρ_f (Γ↓ Γ (dom ρ_f))))]
    [(-Clo  xs e ρ_f Γ_f) (with-guarded-arity (↦β xs e ρ_f Γ_f))]
    [(-Ar (-=>i xs cs γs rst d ρ_c Γ_c) α l³)
     (when rst
       (error '↦@ "varargs"))
     (match/nd: ((Listof -V) → -Δς) (σ@/list σ γs) ; TODO can explode very fast!!
       [Cs (match/nd: (-V → -Δς) (σ@ σ α)
             [V_g (with-guarded-arity (↦indy xs cs Cs d ρ_c Γ_c V_g l³))])])]
    [(-●) (with-guarded-arity (set-add (↦havoc) (↦opq)))]
    [_ (-Δς (-blm l 'apply 'procedure? (list V_f)) Γ κ '() '() '())]))

(: rt-spurious? ([-M -σ -φ.rt.@ -Γ] [-WVs] . ->* . Boolean))
;; Check whether a returned result is spurious
(define (rt-spurious? M σ φ Γ [W (-W '() #f)])
  (match-define (-W Vs ?e) W)
  (match-define (-φ.rt.@ Γ₀ xs e_f e_xs) φ)
  (define params ; only care params that have corresponding args
    (for/set: : (Setof Symbol) ([x xs] [e_x e_xs] #:when e_x) x))

  ; Convert invariants about parameters in new environment
  ; to invariants about arguments in old environment
  ; PRECOND: (FV e) ⊆ xs
  (define convert
    (e/map
     (for/hash : (HashTable -e -e) ([x xs] [e_x e_xs] #:when e_x)
       (values (-x x) e_x))))
  
  (define facts*
    (for/set: : -es ([e (-Γ-facts Γ)] #:when (⊆ (FV e) params))
      (convert e)))

  ; Check whether the propositions would contradict
  (define Γ₀* (MσΓ⊓ M σ Γ₀ facts*))
  (define ans
    (cond
      [Γ₀* (or (spurious? M σ Γ₀* (-W Vs (and ?e (convert ?e))))
               (spurious? M σ Γ₀* (-W Vs (apply -?@ e_f e_xs))))]
      [else #t]))
  
  (begin ;; debug
    (dbg 'rt "Return from: ~a~n"
         `(,(show-?e e_f)
           ,@(for/list : (Listof Sexp) ([x xs] [e_x e_xs])
               `(,x ↦ ,(show-?e e_x)))))
    (dbg 'rt "Caller knows: ~a~n" (show-Γ Γ₀))
    (dbg 'rt "Callee knows: ~a~n" (show-Γ Γ))
    (dbg 'rt "Caller would know: ~a~n" (and Γ₀* (show-Γ Γ₀*)))
    (dbg 'rt "Spurious? ~a~n~n" ans))
  ans)
