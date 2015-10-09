#lang typed/racket/base

(require
 racket/match racket/set racket/function
 "../utils.rkt" "../ast.rkt" "../runtime.rkt" "../provability.rkt" "../delta.rkt" "../machine.rkt"
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

  (define-syntax-rule (with-guarded-arity n e ...)
    (cond
      [(= n (length W_xs)) e ...]
      [else
       (-Δς (-blm l 'Λ (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤) V_xs)
            Γ κ '() '() '())]))

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

  (: ↦δ : -o → -Δς*)
  (define (↦δ o)
    (match/nd: (-AΓ → -Δς) (δ M σ Γ o W_xs (-src-loc-party loc))
      [(-AΓ (? -blm? blm) Γ*) (-Δς blm         Γ* κ '() '() '())]
      [(-AΓ (? list? Vs ) Γ*) (-Δς (-W Vs e_a) Γ* κ '() '() '())]))
  
  (: ↦havoc : → (Setof -Δς))
  (define (↦havoc)
    (define V_havoc (σ@₁ σ (-α.def -havoc-id)))
    (define W_havoc (-W V_havoc (-ref -havoc-id l 0)))
    (for/fold ([acc : (Setof -Δς) ∅]) ([W_x W_xs])
      (match (↦@ W_havoc (list W_x) Γ κ σ Ξ M -Λ)
        [(? set? s) (∪ acc s)]
        [(? -Δς? ς) (set-add acc ς)])))

  (: ↦opq : → -Δς)
  (define (↦opq) (-Δς (-W (list '•) e_a) Γ κ '() '() '()))

  (: ↦indy : (Listof Symbol) (Listof -?e) (Listof -V) -e -ρ -Γ -V Mon-Info → -Δς*)
  (define (↦indy xs cs Cs d ρ_d Γ_d V_g l³)
    (define D (-⇓ d ρ_d))
    ;; TODO: probably don't need these restoring frames anymore. Check again.
    (define κ₁ (-kont (-φ.rt.@ Γ xs e_f e_xs) κ))
    (match* (xs cs Cs W_xs)
      [('() '() '() '())
       (define κ₂ (-kont (-φ.indy.rng V_g '() l³ pos) κ₁))
       (-Δς (-⇓ d ρ_d) Γ_d κ₂ '() '() '())]
      [((cons x xs*) (cons c cs*) (cons C Cs*) (cons W_x W_xs*))
       (define l³* (swap-parties l³))
       (define W_c (-W C c))
       (define W_x* (-W (-W-x W_x) (-x x)))
       (define κ₂ (-kont (-φ.indy.dom x xs* cs* Cs* W_xs* '() V_g d ρ_d l³ pos) κ₁))
       (↦mon W_c W_x* Γ_d κ₂ σ Ξ M l³* pos)]))

  (: ↦con : -st-mk → -Δς)
  (define (↦con k)
    (match-define (-st-mk (and s (-struct-info id n _))) k)
    (with-guarded-arity n
      (define αs (alloc-fields s pos W_xs))
      (define δσ : -Δσ
        (for/list ([α αs] [W W_xs])
          (cons α (close-Γ Γ (-W-x W)))))
      (-Δς (-W (list (-St s αs)) e_a) Γ κ δσ '() '())))

  (: ↦ac : -st-ac → -Δς*)
  (define (↦ac o)
    (match-define (-st-ac (and s (-struct-info id n _)) i) o)
    (with-guarded-arity 1
      (match-define (list (and W (-W V e))) W_xs)
      (define prd (-st-p s))
      (define-values (Γ-ok Γ-bad) (Γ+/-W∋Ws M σ Γ (-W prd prd) W))
      (define δς-ok
        (and
         Γ-ok
         (match V
           [(-St _ αs)
            (for/set: : (Setof -Δς) ([V (σ@ σ (list-ref αs i))])
              (-Δς (-W (list V) e_a) Γ-ok κ '() '() '()))]
           [(-St/checked s γs l³ α)
            (define φ-select (-φ.@ '() (list (-W o o)) -Λ))
            (define e_x (car e_xs))
            (cond
              [(list-ref γs i) =>
               (λ ([γ : -α])
                 (for/set: : (Setof -Δς) ([C* (σ@ σ γ)] [V* (σ@ σ α)])
                   (define φ-mon (-φ.mon.v (-W C* #f) l³ pos))
                   (define κ* (-kont* φ-select φ-mon κ))
                   (-Δς (-W (list V*) e_x) Γ-ok κ* '() '() '())))]
              [else
               (define κ* (-kont φ-select κ))
               (for/set: : (Setof -Δς) ([V* (σ@ σ α)])
                 (-Δς (-W (list V*) e_x) Γ-ok κ* '() '() '()))])]
           [_ (-Δς (-W (list '•) e_a) Γ-ok κ '() '() '())])))
      (define δς-bad
        (and Γ-bad (-Δς (-blm l (show-o o) prd (list V)) Γ-bad κ '() '() '())))
      (collect δς-ok δς-bad)))

  (: ↦mut : -st-mut → -Δς*)
  (define (↦mut o)
    (with-guarded-arity 2
      (match-define (-st-mut s i) o)
      (match-define (list (and W₁ (-W V₁ e₁)) (-W V₂ e₂)) W_xs)
      (define prd (-st-p s))
      (define-values (Γ-ok Γ-bad) (Γ+/-W∋Ws M σ Γ (-W prd prd) W₁))
      (define δς-bad
        (and Γ-bad (-Δς (-blm l (show-o o) prd (list V₁)) Γ-bad κ '() '() '())))
      (define δς-ok
        (and Γ-ok
             (match V₁
               [(-St _ αs)
                (define δσ (list (cons (list-ref αs i) V₂)))
                (-Δς (-W -Void/Vs e_a) Γ-ok κ δσ '() '())]
               [(-St/checked s γs (and l³ (list l+ l- lo)) α)
                (define e_x (car e_xs))
                (cond
                  [(list-ref γs i) =>
                   (λ ([γ : -α])
                     (define l³* (list l- l+ lo))
                     (for/set: : (Setof -Δς) ([C* (σ@ σ γ)] [V* (σ@ σ α)])
                       (define φ-mon (-φ.mon.v (-W C* #f) l³* pos))
                       (define φ-mut
                         (-φ.@ '() (list (-W o o) (-W V* e₁)) (-src-loc lo pos)))
                       (define κ* (-kont* φ-mon φ-mut κ))
                       (-Δς (-W (list V₂) e₂) Γ-ok κ* '() '() '())))]
                  [else
                   (for/set: : (Setof -Δς) ([V* (σ@ σ α)])
                     (define φ-mut
                       (-φ.@ '() (list (-W o o) (-W V* e₁)) (-src-loc lo pos)))
                     (define κ* (-kont φ-mut κ))
                     (-Δς (-W (list V*) e_x) Γ-ok κ* '() '() '()))])]
               [_
                ;; TODO: unsound if V₂ concrete buggy higher-order and V₁ opaque
                (-Δς (-W -Void/Vs e_a) Γ-ok κ '() '() '())])))
      (collect δς-ok δς-bad)))

  (: ↦vector : → -Δς*)
  (define (↦vector)
    (define αs
      (for/list : (Listof -α.vct) ([W W_xs] [i (in-naturals)])
        (-α.vct pos i)))
    (define δσ
      (for/list : -Δσ ([α αs] [W W_xs])
        (cons α (close-Γ Γ (-W-x W)))))
    (-Δς (-W (list (-Vector αs)) e_a) Γ κ δσ '() '()))

  (: with-vector-bound-check : -M -σ -Γ -WV -WV (-Γ → -Δς*) → -Δς*)
  (define (with-vector-bound-check M σ Γ W-vec W-idx mk-ok)
    (match-define (-W V-vec e-vec) W-vec)
    (match-define (-W V-idx _    ) W-idx)
    (define e-len (-?@ 'vector-length e-vec))
    (define V-len
      (match V-vec
        [(-Vector αs) (-b (length αs))]
        [_ '•]))
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
                  (blm (-Clo '(x) (-@ '< (list (-x 'x) (or e-len (-W-x W-len))) -Λ) -ρ⊥ -Γ⊤) V-idx))))
    (collect ans-ok ans-bads))

  (: ↦vector-ref : → -Δς*)
  (define (↦vector-ref)
    (with-guarded-arity 2
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
                 (for/fold ([acc : (Setof -Δς) ∅]) ([α αs] [i (in-naturals)])
                   (define ψ (-?@ '= e-idx (-b i)))
                   (match (MσΓ⊢e M σ Γ-ok ψ)
                     ['X acc]
                     [_
                      (define Γ* (Γ+ Γ-ok ψ))
                      (for/fold ([acc : (Setof -Δς) acc]) ([V (σ@ σ α)])
                        (set-add acc (-Δς (-W (list V) e_a) Γ* κ '() '() '())))]))])]
             [(-Vector/checked γs l³ α)
              (for/fold ([acc : (Setof -Δς) ∅]) ([V (σ@ σ α)])
                (for/fold ([acc : (Setof -Δς) acc]) ([γ γs] [i (in-naturals)])
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
             [_ (-Δς (-W (list '•) e_a) Γ-ok κ '() '() '())])))))

  (: ↦vector-set! : → -Δς*)
  (define (↦vector-set!)
    (with-guarded-arity 3
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
              (-Δς (-W -Void/Vs e_a) Γ-ok κ δσ '() '())]
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
              (-Δς (-W -Void/Vs e_a) Γ-ok κ '() '() '())])))))

  (match V_f
    [(? -st-mk? k) (↦con k)]
    [(? -st-ac? o) (↦ac o)]
    [(? -st-mut? o) (↦mut o)]
    ['vector (↦vector)]
    ['vector-ref (↦vector-ref)]
    ['vector-set! (↦vector-set!)]
    [(? -o? o) (↦δ o)]
    [(-Clo* xs e ρ_f    ) (↦β xs e ρ_f (Γ↓ Γ (dom ρ_f)))]
    [(-Clo  xs e ρ_f Γ_f) (↦β xs e ρ_f Γ_f)]
    [(-Ar xs cs γs d ρ_c Γ_c α l³)
     (match/nd: ((Listof -V) → -Δς) (σ@/list σ γs) ; TODO can explode very fast!!
       [Cs (match/nd: (-V → -Δς) (σ@ σ α)
             [V_g (↦indy xs cs Cs d ρ_c Γ_c V_g l³)])])]
    ['• (set-add (↦havoc) (↦opq))]
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
  (define (convert [e : -e]) : -e
    (for/fold ([e e]) ([x xs] [e_x e_xs] #:when e_x)
      (e/ e x e_x)))
  
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
