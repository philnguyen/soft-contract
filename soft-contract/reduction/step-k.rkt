#lang typed/racket/base

(require
 racket/match racket/set racket/function
 "../utils/map.rkt" "../utils/non-det.rkt" "../utils/set.rkt" "../utils/list.rkt" "../utils/debug.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/val.rkt" "../runtime/summ.rkt" "../runtime/path-inv.rkt" "../runtime/addr.rkt"
 "../runtime/simp.rkt" "../runtime/env.rkt" "../runtime/store.rkt"
 "../proof-relation/main.rkt"
 "../machine/definition.rkt"
 "step-e.rkt" "step-app.rkt" "step-mon.rkt")

(provide ↦κ ↦blm)

(: ↦κ : -WVs -Γ -κ -σ -Ξ -M → -Δς*)
(define (↦κ WVs Γ κ σ Ξ M)
  (match κ
    [(and τ (-τ e _ _))
     (match-define (-W _ ?e) WVs)
     (define res (-Res ?e (-Γ-facts Γ)))
     (define M* (⊔ M e res))
     (match/nd: (-kont → -Δς) (hash-ref Ξ τ)
       [(-kont φ κ*)
        (with-Δ '() '() (list (cons e res)) (↦φ WVs Γ φ κ* σ Ξ M*))])]
    [(-kont φ κ*) (↦φ WVs Γ φ κ* σ Ξ M)]))

(: ↦φ : -WVs -Γ -φ -κ -σ -Ξ -M → -Δς*)
;; Stepping rules for "apply" states
(define (↦φ W Γ φ κ σ Ξ M)
  (match-define (-W Vs ?e) W)
  ;; Leave `M` alone for now. TODO: update it.

  (define-syntax-rule (with-guarded-arity n l+ lo e ...)
    (let ([n* n])
      (cond
        [(= n* (length Vs)) e ...]
        [else
         (-Δς (-blm l+ lo
                   (-Clo '(x) (-@ '= (list (-x 'x) (-b n*)) -Λ) -ρ⊥ -Γ⊤)
                   Vs)
             Γ κ '() '() '())])))
  
  (match φ
    ;; top
    [(-φ.top itms e)
     (match itms
       ['() (↦e e -ρ⊥ Γ κ σ Ξ M)]
       [(cons itm itms*)
        (-Δς itm Γ (-kont (-φ.top itms* e) κ) '() '() '())])]
    [(-φ.def l xs)
     (define n (length xs))
     (with-guarded-arity n l 'Λ
       (define-values (δσ ids)
         (for/lists ([δσ : -Δσ] [ids : (Listof -id)])
                    ([x xs] [V Vs])
           (define id (-id x l))
           (values (cons (-α.def id) V) id)))
       (define e?s (split-values ?e n))
       (define Γ*
         (for/fold ([Γ : -Γ Γ]) ([id ids] [e?i e?s])
           (Γ-bind Γ id e?i)))
       (-Δς -Void/W Γ* κ δσ '() '()))]
    [(-φ.ctc l itms x)
     (with-guarded-arity 1 l 'Λ
       (define δσ (list (cons (-α.ctc (-id x l)) (car Vs))))
       (match itms
         ['()
          (-Δς -Void/W Γ κ δσ '() '())]
         [(cons (-p/c-item x* c*) itms*)
          (define κ* (-kont (-φ.ctc l itms* x*) κ))
          (with-Δ δσ '() '()
            (↦e c* -ρ⊥ Γ κ* σ Ξ M))]))]
    ;; Conditional
    [(-φ.if E₁ E₂)
     (match Vs
       [(list V)
        ;(printf "scrutiny is ~a~n" (show-?e ?e))
        (define-values (Γ_t Γ_f) (Γ+/-W M σ Γ (-W V ?e)))
        (define ς_t (and Γ_t (-Δς E₁ Γ_t κ '() '() '())))
        (define ς_f (and Γ_f (-Δς E₂ Γ_f κ '() '() '())))
        (cond
          [(and ς_t ς_f) {set ς_t ς_f}]
          [ς_t ς_t]
          [else (assert ς_f)])]
       [_ (error '↦WVs "TODO: catch wrong arity in conditional")])]
    ;; let-values
    [(-φ.let-values xs bnds bnds↓ ρ e l)
     (define n (length xs))
     (with-guarded-arity n l 'let-values
       (define bnds↓*
         (for/fold ([bnds↓* : (Map Symbol -WV) bnds↓])
                   ([x xs] [V Vs] [ei (split-values ?e n)])
           (hash-set bnds↓* x (-W V ei))))
       (match bnds
         ;; Proceed to let's body
         ['()
          (define-values (ρ* Γ* σ* δσ)
            (for/fold ([ρ* : -ρ ρ] [Γ* : -Γ Γ] [σ* : -σ σ] [δσ : -Δσ '()])
                      ([(x W) (in-hash bnds↓*)])
              (match-define (-W V ex) W)
              (define α (-α.x (cons x Γ)))
              (values (ρ+ ρ* x α)
                      (Γ-bind Γ* x ex)
                      (⊔ σ* α V)
                      (cons (cons α V) δσ))))
          (with-Δ δσ '() '() (↦e e ρ* Γ* (-kont (-φ.rt.let (dom ρ)) κ) σ* Ξ M))]
         ;; Proceed to next assigning clause
         [(cons (cons xs* e*) bnds*)
          (↦e e* ρ Γ (-kont (-φ.let-values xs* bnds* bnds↓* ρ e l) κ) σ Ξ M)]))]
    ;; letrec-values
    [(-φ.letrec-values xs bnds ρ e l)
     (define n (length xs))
     (with-guarded-arity n l 'letrec-values
       (define-values (Γ* σ* δσ)
         (for/fold ([Γ* : -Γ Γ] [σ* : -σ σ] [δσ : -Δσ '()])
                   ([x xs] [V Vs] [ex (split-values ?e n)])
           (define α (ρ@ ρ x))
           (values (Γ-bind Γ* x ex)
                   (⊔ σ* α V)
                   (cons (cons α V) δσ))))
       (match bnds
         ;; proceed to letrec's body
         ['()
          (with-Δ δσ '() '() (↦e e ρ Γ* κ σ* Ξ M))]
         ;; proceed to next assigning clause
         [(cons (cons xs* e*) bnds*)
          (with-Δ δσ '() '()
            (↦e e* ρ Γ* (-kont (-φ.letrec-values xs* bnds* ρ e l) κ) σ* Ξ M))]))]
    [(-φ.set! x α)
     (with-guarded-arity 1 'TODO 'set!
       (define Γ* (Γ-reset Γ x ?e))
       (-Δς -Void/W Γ* κ (list (cons α (car Vs))) '() '()))]
    ;; Application
    [(-φ.@ Es WVs↓ loc)
     (match-define (-src-loc l pos) loc)
     (with-guarded-arity 1 l 'apply
       (match-define (list V) Vs)
       (define WVs↓* (cons (-W V ?e) WVs↓))
        (match Es
          ['()
           (match-define (cons W_f W_xs) (reverse WVs↓*))
           (↦@ W_f W_xs Γ κ σ Ξ M loc)]
          ;; Swap next argument for evaluation
          [(cons E* Es*)
           (-Δς E* Γ (-kont (-φ.@ Es* WVs↓* loc) κ) '() '() '())]))]
    ;; Begin
    [(-φ.begin es ρ)
     (match es
       [(list) (-Δς -Void/W Γ κ '() '() '())]
       [(list e) (↦e e ρ Γ κ σ Ξ M)]
       [(cons e es*)
        (↦e e ρ Γ (-kont (-φ.begin es* ρ) κ) σ Ξ M)])]
    ;; begin0
    ; waiting on first clause
    [(-φ.begin0v es ρ)
     (match es
       ['() (-Δς W Γ κ '() '() '())]
       [(cons e es*)
        (↦e e ρ Γ (-kont (-φ.begin0e W es* ρ) κ) σ Ξ M)])]
    ; waiting on next clause (and discard)
    [(-φ.begin0e W es ρ)
     (match es
       ['() (-Δς W Γ κ '() '() '())]
       [(cons e es*)
        (↦e e ρ Γ (-kont (-φ.begin0e W es* ρ) κ) σ Ξ M)])]
    ;; mon
    ; waiting on the contract
    [(-φ.mon.c E (and l³ (list _ _ lo)) pos)
     (with-guarded-arity 1 lo 'Λ
       (match-define (list C) Vs)
       (define W_C (-W C ?e))
       (cond
         [(-WV? E) (↦mon W_C E Γ κ σ Ξ M l³ pos)]
         [else (-Δς E Γ (-kont (-φ.mon.v W_C l³ pos) κ) '() '() '())]))]
    ; waiting on the value to be checked
    [(-φ.mon.v C (and l³ (list l+ _ lo)) pos)
     (with-guarded-arity 1 l+ lo
       (match-define (list V) Vs)
       (define W_V (-W V ?e))
       (cond
         [(-WV? C) (↦mon C W_V Γ κ σ Ξ M l³ pos)]
         [else (-Δς C Γ (-kont (-φ.mon.c W_V l³ pos) κ) '() '() '())]))]
    ;; indy
    [(-φ.indy.dom x args doms↓ Rst V_f d ρ_d l³ pos)
     (with-guarded-arity 1 'Λ 'Λ
       (match-define (list V) Vs)
       (define l³* (swap-parties l³))
       (define doms↓* (cons (cons x (-W V ?e)) doms↓))
       (match args
         ['()
          (define doms (reverse doms↓*))
          (match Rst
            [(list x* W_c* W_vs)
             (define-values (Vs es) ((inst unzip-by -WV -V -?e) -W-x -W-e W_vs))
             (define-values (δσ V-rst) (alloc-varargs Γ Vs pos))
             (define e-rst (-?list es))
             (define κ* (-kont (-φ.indy.rst x* doms V_f d ρ_d l³ pos) κ))
             ; (postpone allocating init args until later)
             (with-Δ δσ '() '()
               (↦mon W_c* (-W V-rst e-rst) Γ κ* σ Ξ M l³* pos))]
            [#f
             (define-values (args zs Vs)
               (for/lists ([args : (Listof -WV)] [zs : (Listof Symbol)] [Vs : (Listof -V)])
                          ([dom doms])
                 (match-define (cons x (and W (-W V_x e_x))) dom)
                 (values W x V_x)))
             (define-values (δσ ρ_d*) (alloc Γ ρ_d zs Vs pos))
             (with-Δ δσ '() '()
               (↦e d ρ_d* Γ (-kont (-φ.indy.rng V_f args #f l³ pos) κ) σ Ξ M))])]
         [(cons (list x* (and W_c* (-W C* c*)) (-W V_x e_x)) args*)
          (define κ* (-kont (-φ.indy.dom x* args* doms↓* Rst V_f d ρ_d l³ pos) κ))
          (define W_x* (-W V_x (canonicalize Γ (-x x*))))
          (↦mon W_c* W_x* Γ κ* σ Ξ M l³* pos)]))]
    [(-φ.indy.rst x* doms V_f d ρ_d l³ pos)
     (with-guarded-arity 1 'Λ 'Λ
       (define-values (δσ₀ ρ_d₀) (alloc Γ ρ_d (list x*) Vs pos))
       (define-values (args xs₀ Vs₀)
         (for/lists ([args : (Listof -WV)] [xs : (Listof Symbol)] [Vs : (Listof -V)])
                    ([dom doms])
           (match-define (cons x (and W (-W V_x e_x))) dom)
           (values W x V_x)))
       (define-values (δσ₁ ρ_d₁) (alloc Γ ρ_d₀ xs₀ Vs₀ pos))
       (with-Δ (append δσ₀ δσ₁) '() '()
         (↦e d ρ_d₁ Γ (-kont (-φ.indy.rng V_f args (-W (car Vs) ?e) l³ pos) κ) σ Ξ M)))]
    [(-φ.indy.rng W_f args Rst l³ pos)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (match-define (list V) Vs)
       (define W_d (-W V ?e))
       (define κ* (-kont (-φ.mon.v W_d l³ pos) κ))
       (match Rst
         [(and W-rst (-W V-rst e-rst))
          (match/nd: ((Listof -V) → -Δς) (unalloc-varargs σ V-rst)
            [Vs-rst
             (define es-rst (-?unlist e-rst (length Vs-rst)))
             (define Ws-rst (map (inst -W -V) Vs-rst es-rst))
             (↦@ W_f (append args Ws-rst) Γ κ* σ Ξ M (-src-loc lo pos))])]
         [#f
          (↦@ W_f args Γ κ* σ Ξ M (-src-loc lo pos))]))]
    [(-φ.mon.struct s γs cs i Ws↓ W l³ pos)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (match-define (list V) Vs)
       (define Ws↓* (cons (-W V ?e) Ws↓))
       (match cs
         ['()
          (match-define (-struct-info _ n mutables) s)
          (define Ws (reverse Ws↓*))
          (define-values (Vs es)
            (for/lists ([Vs : (Listof -V)] [es : (Listof -?e)])
                       ([W Ws])
              (values (-W-x W) (-W-e W))))
          (define αs (alloc-fields s es pos))
          (define V-inner (-St s αs))
          (define δσ (map (inst cons -α -V) αs Vs))
          (define e_a (apply -?@ (-st-mk s) es))
          
          ; If struct has 1+ mutable fields, wrap the contract before returning
          (define-values (V* δσ*)
            (cond
              [(set-empty? mutables) (values V-inner δσ)]
              [else
               (define α (-α.st* (-struct-info-id s) pos))
               (define δσ* (cons (cons α V-inner) δσ))
               (define γs*
                 (for/list : (Listof (Option -α.struct/c)) ([(γ i) (in-indexed γs)])
                   (and (∋ mutables i) γ)))
               (define V-wrapped (-St/checked s γs* l³ α))
               (values V-wrapped δσ*)]))
          (-Δς (-W (list V*) e_a) Γ κ δσ* '() '())]
         [(cons c cs*)
          (define i* (+ i 1))
          (define φ₁ (-φ.mon.struct s γs cs* i* Ws↓* W l³ pos))
          (define φ₃ (-φ.@ '() (list (-W (-st-ac s i*) #f)) (-src-loc 'Λ pos)))
          (for/set: : (Setof -Δς) ([C (σ@ σ (list-ref γs i*))])
            (define φ₂ (-φ.mon.v (-W C c) l³ pos))
            (define κ* (-kont* φ₃ φ₂ φ₁ κ))
            (-Δς (-W (list (-W-x W)) (-W-e W)) Γ κ* '() '() '()))]))]
    [(-φ.mon.vector/c γs cs i W l³ pos)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (match cs
         ['()
          (define α (-α.vct pos))
          (match-define (-W V-inner e-inner) W)
          (define δσ (list (cons α V-inner)))
          (define V/wrapped (-Vector/checked γs l³ α))
          (-Δς (-W (list V-inner) e-inner) Γ κ δσ '() '())]
         [(cons c cs*)
          (define i* (+ 1 i))
          (define φ-chk-rest (-φ.mon.vector/c γs cs* i* W l³ pos))
          (define φ-ref (-φ.@ '() (list W -vector-ref/W) -Λ))
          (for/set: : (Setof -Δς) ([C (σ@ σ (list-ref γs i*))])
            (define φ-chk (-φ.mon.v (-W C c) l³ pos))
            (define κ* (-kont* φ-ref φ-chk φ-chk-rest κ))
            (-Δς (-W (list (-b i*)) (-b i*)) Γ κ* '() '() '()))]))]
    [(-φ.mon.vectorof (cons γ W-c) n i W l³ pos)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (define i* (+ 1 i))
       (cond
         [(< i* n)
          (define φ-chk-rest (-φ.mon.vectorof (cons γ W-c) n i* W l³ pos))
          (define φ-chk (-φ.mon.v W-c l³ pos))
          (define φ-ref (-φ.@ '() (list W -vector-ref/W) -Λ))
          (define κ* (-kont* φ-ref φ-chk φ-chk-rest κ))
          (-Δς (-W (list (-b i*)) (-b i*)) Γ κ* '() '() '())]
         [else
          (define α (-α.vct pos))
          (match-define (-W V-inner e-inner) W)
          (define δσ (list (cons α V-inner)))
          (define V/wrapped (-Vector/same γ l³ α))
          (-Δς (-W (list V-inner) e-inner) Γ κ δσ '() '())]))]
    ;; Accumulate higher-order contracts with passing first-order checks
    [(-φ.filter-fo W_Cs W_Cs↓ W_C (and W_v (-W V_v e_v)) (and l³ (list l+ l- lo)) pos)
     (define-values (Γ_t Γ_f) (Γ+/-W M σ Γ (-W (car Vs) ?e)))
     (define δς_t : (Option -Δς)
       (and Γ_t
            (let ()
              (define W_Cs↓* (cons W_C W_Cs↓))
              (match W_Cs
                ['()
                 (match W_Cs↓*
                   ['()
                    (-Δς (-blm l+ lo '|or/c (none passed)| (list V_v)) Γ_t κ '() '() '())]
                   [(list W_C)
                    (define κ* (-kont (-φ.mon.v W_C l³ pos) κ))
                    (-Δς (-W (list V_v) e_v) Γ_t κ* '() '() '())]
                   [_
                    (-Δς (-blm l+ lo '|or/c (first-order-ly indistinguishable)| (list V_v))
                         Γ_t κ '() '() '())])]
                [(cons W_C* W_Cs*)
                 (define κ*
                   (-kont*
                    (-φ.filter-fo W_Cs* W_Cs↓* W_C* W_v l³ pos)
                    (-φ.@ '() (list -contract-first-order-passes?/W W_C*) (-src-loc lo pos))
                    κ))
                 (-Δς (-W (list V_v) e_v) Γ_t κ* '() '() '())]))))
     (define δς_f : (Option -Δς)
       (and Γ_f
            (let ()
              (match W_Cs
                ['()
                 (match W_Cs↓
                   ['()
                    (-Δς (-blm l+ lo '|or/c (none passed)| (list V_v)) Γ_f κ '() '() '())]
                   [(list W_C)
                    (define κ* (-kont (-φ.mon.v W_C l³ pos) κ))
                    (-Δς (-W (list V_v) e_v) Γ_f κ* '() '() '())]
                   [_
                    (-Δς (-blm l+ lo '|or/c (first-order-ly indistinguishable)| (list V_v))
                         Γ_f κ '() '() '())])]
                [(cons W_C* W_Cs*)
                 (define κ*
                   (-kont*
                    (-φ.filter-fo W_Cs* W_Cs↓ W_C* W_v l³ pos)
                    (-φ.@ '() (list -contract-first-order-passes?/W W_C*) (-src-loc lo pos))
                    κ))
                 (-Δς (-W (list V_v) e_v) Γ_f κ* '() '() '())]))))
     (cond
       [(and δς_t δς_f) {set δς_t δς_f}]
       [δς_t δς_t]
       [else (assert δς_f)])]
    ;; restore path invariant in previous context
    [(-φ.rt.@ Γ₀ xs* e_f e_xs*)
     (cond
       [(rt-strengthen M σ φ Γ (-W Vs ?e)) =>
        (λ ([Γ₀* : -Γ])
          (define-values (xs e_xs) (bind-args xs* e_xs*))
          (define e_a
            (cond
              [(-λ? e_f)
               (and ?e
                    (andmap (λ (x) x) e_xs)
                    (e/list (map -x xs) (cast e_xs (Listof -e)) ?e))]
              [else
               (or
                ; take answer as `(f x …)` if possible
                (apply -?@ e_f e_xs)
                ; otherwise [e/e_x…]a
                ; TODO: confirm this won't blow up
                (and ?e
                     (andmap (λ (x) x) e_xs)
                     (e/list (map -x xs) (cast e_xs (Listof -e)) ?e)))]))
          (-Δς (-W (close-Γ Γ Vs) e_a) Γ₀* κ '() '() '()))]
       [else ∅])
     
     #;(cond [(rt-spurious? M σ φ Γ (-W Vs ?e)) ∅]
           [else
            (define-values (xs e_xs) (bind-args xs* e_xs*))
            (define e_a
              (or
               ; take answer as `(f x …)` if possible,
               (apply -?@ e_f e_xs)
               ; otherwise a[x/e_x…]
               ; TODO: confirm this won't blow up
               (and ?e
                    (andmap (λ (x) x) e_xs)
                    (e/list (map -x xs) (cast e_xs (Listof -e)) ?e))))
            (-Δς (-W (close-Γ Γ Vs) e_a) Γ₀ κ '() '() '())])]
    [(-φ.rt.let dom₀)
     (define e* (and ?e (⊆ (FV ?e) dom₀) ?e))
     (define Γ* (Γ↓ Γ dom₀))
     (-Δς (-W (close-Γ Γ Vs) e*) Γ* κ '() '() '())]
    ;; contract stuff
    [(-φ.μ/c x)
     (with-guarded-arity 1 'TODO 'Λ
       (match-define (list V) Vs)
       (define δσ (list (cons (-α.x/c x) V)))
       (define ?c (-?μ/c x ?e))
       (-Δς (-W (list V) (and ?e ?c (unroll x ?c ?e))) Γ κ δσ '() '()))]
    [(-φ.struct/c s es ρ WVs↓ pos)
     (with-guarded-arity 1 'TODO 'Λ
       (match-define (-struct-info id n _) s)
       (match-define (list V) Vs)
       (define WVs↓* (cons (-W V ?e) WVs↓))
       (match es
         ['()
          (define n (length WVs↓*))
          (define id (-struct-info-id s))
          (define-values (αs σ* es* δσ flat?)
            ; accumulate new store and address list
            ; which is reversed compard to `WVs↓*`, hence of the right order
            (for/fold ([αs : (Listof -α.struct/c) '()]
                       [σ* : -σ σ]
                       [es* : (Listof -?e) '()]
                       [δσ : -Δσ '()]
                       [flat? : Boolean #t])
                      ([WV WVs↓*] [i (in-range n)])
              (match-define (-W V e) WV)
              (define α (-α.struct/c (or e (list id pos i))))
              (values (cons α αs)
                      (⊔ σ* α V)
                      (cons e es*)
                      (cons (cons α V) δσ)
                      (and flat? (C-flat? V)))))
          (define C (-St/C flat? s αs))
          (define e_C (-?struct/c s es*))
          (-Δς (-W (list C) e_C) Γ κ δσ '() '())]
         [(cons e es*)
          (↦e e ρ Γ (-kont (-φ.struct/c s es* ρ WVs↓* pos) κ) σ Ξ M)]))]
    [(-φ.=>i cs WCs↓ xs rst rng ρ pos)
     (with-guarded-arity 1 'TODO 'Λ
       (match-define (list V) Vs)
       (match cs
         ['()
          (match rst
            [(cons x* e*)
             (define WCs↓* (cons (-W V ?e) WCs↓))
             (↦e e* ρ Γ (-kont (-φ.=>i '() WCs↓* xs x* rng ρ pos) κ) σ Ξ M)]
            [(? symbol? x*)
             (define-values (Doms₀ cs₀ δσ₀)
               (for/lists ([Doms : (Listof (Pairof Symbol -α.dom))] [cs* : (Listof -?e)] [δσ : -Δσ])
                          ([(WC i) (in-indexed (reverse WCs↓))] [x xs])
                 (match-define (-W C c) WC)
                 (define γ (-α.dom (or c (cons pos i))))
                 (values (cons x γ) c (cons γ C))))
             (define γ* (-α.rst (or ?e pos)))
             (define δσ (cons (cons γ* V) δσ₀))
             (define C (-=>i Doms₀ (cons x* γ*) rng ρ Γ))
             (define e_C (-?->i* xs cs₀ x* ?e rng))
             (-Δς (-W (list C) e_C) Γ κ δσ '() '())]
            [#f
             (define WCs↓* (cons (-W V ?e) WCs↓))
             (define-values (Doms cs* δσ)
               (for/lists ([Doms : (Listof (Pairof Symbol -α.dom))] [cs* : (Listof -?e)] [δσ : -Δσ])
                          ([(WC i) (in-indexed (reverse WCs↓*))] [x xs])
                 (match-define (-W C c) WC)
                 (define γ (-α.dom (or c (cons pos i))))
                 (values (cons x γ) c (cons γ C))))
             (define C (-=>i Doms #f rng ρ Γ))
             (define e_C (-?->i xs cs* rng))
             (-Δς (-W (list C) e_C) Γ κ δσ '() '())])]
         [(cons c cs*)
          (define WCs↓* (cons (-W V ?e) WCs↓))
          (↦e c ρ Γ (-kont (-φ.=>i cs* WCs↓* xs rst rng ρ pos) κ) σ Ξ M)]))]
    ))

(: ↦blm : -blm -Γ -κ -σ -Ξ -M → -Δς*)
;; Either propagate error or eliminate a spurious one
(define (↦blm blm Γ κ σ Ξ M)
  (match-define (-blm l+ _ _ _) blm)
  (case l+
    [(Λ † havoc) ∅]
    [else
     (match κ
       [(? -τ? τ) (-Δς blm Γ τ '() '() '())]
       [(-kont φ κ*)
        (match φ
          [(-φ.rt.@ Γ₀ _ _ _)
           (cond
             [(parameterize ([debugs ∅ #;(set 'rt)]) (rt-strengthen M σ φ Γ)) =>
              (λ ([Γ₀* : -Γ]) (-Δς blm Γ₀* κ* '() '() '()))]
             [else ∅])
           #;(cond [(parameterize ([debugs (set 'rt)]) (rt-spurious? M σ φ Γ)) ∅]
                 [else (-Δς blm Γ₀ κ* '() '() '())])]
          [(-φ.rt.let dom) (-Δς blm (Γ↓ Γ dom) κ* '() '() '())]
          [_ (↦blm blm Γ κ* σ Ξ M)])])]))
