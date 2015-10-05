#lang typed/racket/base

(require
 racket/match racket/set
 "../utils.rkt" "../ast.rkt" "../runtime.rkt" "../provability.rkt" "../machine.rkt"
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
        [(= n (length Vs)) e ...]
        [else
         (-Δς (-blm l+ lo
                   (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤)
                   Vs)
             Γ κ '() '() '())])))
  
  (match φ
    ;; Conditional
    [(-φ.if E₁ E₂)
     (match Vs
       [(list V)
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
              (define α x #;(-α.bnd x ex Γ))
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
       ; TODO: might not need to erase `set! x e`
       ; if `e` doesn't depend on mutable state
       (-Δς (-W -Void/Vs #f) Γ* κ (list (cons α (car Vs))) '() '()))]
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
       [(list) (-Δς (-W -Void/Vs -void) Γ κ '() '() '())]
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
    [(-φ.indy.dom x xs cs Cs W_xs doms↓ V_f d ρ_d l³ pos)
     (with-guarded-arity 1 'Λ 'Λ
       (match-define (list V) Vs)
       (define l³* (swap-parties l³))
       (define doms↓* (cons (cons x (-W V ?e)) doms↓))
       (match* (xs cs Cs W_xs)
         [('() '() '() '())
          (define args (map (inst cdr Symbol -WV) (reverse doms↓*))) ; TODO
          (↦e d ρ_d Γ (-kont (-φ.indy.rng V_f args l³ pos) κ) σ Ξ M)]
         [((cons x* xs*) (cons c* cs*) (cons C* Cs*) (cons W_x* W_xs*))
          (define W_c* (-W C* c*))
          (define κ* (-kont (-φ.indy.dom x* xs* cs* Cs* W_xs* doms↓* V_f d ρ_d l³ pos) κ))
          (↦mon W_c* W_x* Γ κ* σ Ξ M l³* pos)]))]
    [(-φ.indy.rng V_f args l³ pos)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (match-define (list V) Vs)
       (define W_d (-W V ?e))
       (define W_f (-W V_f (-x 'f•))) ; FIXME temp. hack
       (define κ* (-kont (-φ.mon.v W_d l³ pos) κ))
       (↦@ W_f args Γ κ* σ Ξ M (-src-loc lo pos)))]
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
          (define αs (alloc-fields s pos Ws))
          (define V-inner (-St s αs))
          (define δσ (map (inst cons -α -V) αs Vs))
          (define e_a (apply -?@ (-st-mk s) es))
          
          ; If struct has 1+ mutable fields, wrap the contract before returning
          (define-values (V* δσ*)
            (cond
              [(set-empty? mutables) (values V-inner δσ)]
              [else
               (define α (-α.wrp (-struct-info-id s) pos))
               (define δσ* (cons (cons α V-inner) δσ))
               (define γs*
                 (for/list : (Listof (Option -α)) ([γ γs] [i (in-naturals)])
                   (and (∋ mutables i) γ)))
               (define V-wrapped (-St/checked s γs* l³ α))
               (values V-wrapped δσ*)]))
          (-Δς (-W (list V*) e_a) Γ κ δσ* '() '())]
         [(cons c cs*)
          (define i* (+ i 1))
          (define ac (-st-ac s i*))
          (define φ₁ (-φ.mon.struct s γs cs* i* Ws↓* W l³ pos))
          (define φ₃ (-φ.@ '() (list (-W ac ac)) (-src-loc 'Λ pos)))
          (for/set: : (Setof -Δς) ([C (σ@ σ (list-ref γs i*))])
            (define φ₂ (-φ.mon.v (-W C c) l³ pos))
            (define κ* (-kont* φ₃ φ₂ φ₁ κ))
            (-Δς (-W (list (-W-x W)) (-W-e W)) Γ κ* '() '() '()))]))]
    [(-φ.mon.vector/c γs cs i W l³ pos)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (match cs
         ['()
          (define α (-α.inv pos))
          (define δσ (list (cons α (-W-x W))))
          (define V/wrapped (-Vector/checked γs l³ α))
          (-Δς (-W (list (-W-x W)) (-W-e W)) Γ κ δσ '() '())]
         [(cons c cs*)
          (define i* (+ 1 i))
          (define φ₁ (-φ.mon.vector/c γs cs* i* W l³ pos))
          (define φ₃ (-φ.@ '() (list W -vector-ref/W) -Λ))
          (for/set: : (Setof -Δς) ([C (σ@ σ (list-ref γs i*))])
            (define φ₂ (-φ.mon.v (-W C c) l³ pos))
            (define κ* (-kont* φ₃ φ₂ φ₁ κ))
            (-Δς (-W (list (-b i*)) (-b i*)) Γ κ* '() '() '()))]))]
    ;; restore path invariant in previous context
    [(-φ.rt.@ Γ₀ xs e_f e_xs)
     (cond [(rt-spurious? M σ φ Γ (-W Vs ?e)) ∅]
           [else
            (define e_a
              ; take answer as `(f x …)` if possible,
              ; otherwise a[x/e_x…]
              ; TODO: confirm this won't blow up
              (or (apply -?@ e_f e_xs)
                  (for/fold ([e_a : -?e ?e]) ([x xs] [e_x e_xs])
                    (and e_a e_x (e/ e_a x e_x)))))
            (-Δς (-W (close-Γ Γ Vs) e_a) Γ₀ κ '() '() '())])]
    [(-φ.rt.let dom₀)
     (define e* (and ?e (⊆ (FV ?e) dom₀) ?e))
     (define Γ* (Γ↓ Γ dom₀))
     (-Δς (-W (close-Γ Γ Vs) e*) Γ* κ '() '() '())]
    ;; contract stuff
    [(-φ.μc x _)
     (match Vs
       [(list V) (error '↦WVs "TODO: μ/c")]
       [_ (error '↦WVs "TODO: catch arity error for μ/c")])]
    [(-φ.struct/c s es ρ WVs↓ pos)
     (with-guarded-arity 1 'TODO 'Λ
       (match-define (-struct-info id n _) s)
       (match-define (list V) Vs)
       (define WVs↓* (cons (-W V ?e) WVs↓))
       (match es
         ['()
          (define n (length WVs↓*))
          (define id/c
            (match id
              [(? symbol? s) (show/c s)]
              [(-id-local s l) (-id-local (show/c s) l)]))
          (define-values (αs σ* es* δσ)
            ; accumulate new store and address list
            ; which is reversed compard to `WVs↓*`, hence of the right order
            (for/fold ([αs : (Listof -α) '()] [σ* : -σ σ] [es* : (Listof -?e) '()] [δσ : -Δσ '()])
                      ([WV WVs↓*] [i (in-range n)])
              (match-define (-W V e) WV)
              (define α (-α.fld id/c pos i))
              (values (cons α αs)
                      (⊔ σ* α V)
                      (cons e es*)
                      (cons (cons α V) δσ))))
          (define C (-St/C s αs))
          (define e_C (-?struct/c s es*))
          (-Δς (-W (list C) e_C) Γ κ δσ '() '())]
         [(cons e es*)
          (↦e e ρ Γ (-kont (-φ.struct/c s es* ρ WVs↓* pos) κ) σ Ξ M)]))]
    [(-φ.=>i cs Cs↓ cs↓ xs rng ρ pos)
     (with-guarded-arity 1 'TODO 'Λ
       (match-define (list V) Vs)
       (define Cs↓* (cons V Cs↓))
       (define cs↓* (cons ?e cs↓))
       (match cs
         ['()
          (define-values (γs σ* cs* δσ)
            ;; accumulate new store and address list for contract domains
            ;; (domains are reversed compared to `Cs↓*`)
            (for/fold ([γs : (Listof -α) '()] [σ* : -σ σ] [cs* : (Listof -?e) '()] [δσ : -Δσ '()])
                      ([C Cs↓*] [c cs↓*] [i (in-naturals)])
              (define γ (-α.fld (-id-local '-> 'Λ) pos i))
              (values (cons γ γs)
                      (⊔ σ* γ C)
                      (cons c cs*)
                      (cons (cons γ C) δσ))))
          (define C (-=>i xs cs* γs rng ρ Γ))
          (define e_C (-?->i xs cs* rng))
          (-Δς (-W (list C) e_C) Γ κ δσ '() '())]
         [(cons c cs*)
          (↦e c ρ Γ (-kont (-φ.=>i cs* Cs↓* cs↓* xs rng ρ pos) κ) σ Ξ M)]))]
    ))

(: ↦blm : -blm -Γ -κ -σ -Ξ -M → -Δς*)
;; Either propagate error or eliminate a spurious one
(define (↦blm blm Γ κ σ Ξ M)
  (match κ
    [(? -τ? τ) (-Δς blm Γ τ '() '() '())]
    [(-kont φ κ*)
     (match φ
       [(-φ.rt.@ Γ₀ _ _ _)
        (cond [(rt-spurious? M σ φ Γ) ∅]
              [else (-Δς blm Γ₀ κ* '() '() '())])]
       [(-φ.rt.let dom) (-Δς blm (Γ↓ Γ dom) κ* '() '() '())]
       [_ (↦blm blm Γ κ* σ Ξ M)])]))
