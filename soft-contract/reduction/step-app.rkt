#lang typed/racket/base

(require
 racket/match racket/set racket/list (except-in racket/function arity-includes?)
 "../utils/list.rkt" "../utils/debug.rkt" "../utils/map.rkt" "../utils/non-det.rkt" "../utils/set.rkt"
 "../utils/untyped-macros.rkt" "../utils/def.rkt" "../utils/pretty.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../runtime/val.rkt" "../runtime/simp.rkt" "../runtime/env.rkt" "../runtime/store.rkt"
 "../runtime/addr.rkt" "../runtime/path-inv.rkt" "../runtime/arity.rkt" "../runtime/summ.rkt"
 "../runtime/simp.rkt"
 "../delta.rkt"
 "../machine/definition.rkt" "../machine/havoc.rkt"
 "../proof-relation/local.rkt" "../proof-relation/main.rkt"
 "step-mon.rkt")

(provide ↦@ rt-strengthen ↦opq ↦opq/verify ↦opq/ce)

(: ↦opq/verify : -?e (Listof -WV) -?e -Γ -κ -σ -Ξ -M -src-loc → (Setof -Δς))
(define (↦opq/verify _ W-xs e-a Γ κ σ Ξ M loc)
  (define δς-● (-Δς (-W -●/Vs e-a) Γ κ '() '() '()))
    (define W-hv
      (let ([V-hv (σ@₁ σ (-α.def -havoc-id))]
            [l (-src-loc-party loc)])
        (-W V-hv (-ref -havoc-id l 0))))
    (for/fold ([acc : (Setof -Δς) {set δς-●}]) ([W-x W-xs])
      (match (↦@ W-hv (list W-x) Γ κ σ Ξ M -Λ)
        [(? set? s) (∪ acc s)]
        [(? -Δς? ς) (set-add acc ς)])))

(: ↦opq/ce : -?e (Listof -WV) -?e -Γ -κ -σ -Ξ -M -src-loc → -Δς*)
(define (↦opq/ce e-f W-xs e-a Γ κ σ Ξ M loc)

  (: ↦opq/ce₁ : -WV → -Δς*)
  (define (↦opq/ce₁ W-x)
    (match-define (-W V-x e-x) W-x)
    
    (define case-const
      (let ([v• (•!)])
        (define fun (-λ '(_) v•))
        (define Γ* (Γ+ Γ (-?@ 'equal? e-f fun) (-?@ 'equal? (-?@ e-f e-x) v•)))
        (-Δς (-W -●/Vs v•) Γ* κ '() '() '())))

    (define case-dep
      (let ([•₁ (•!)]
            [•₂ (•!)])
        (define e
          (-if (-@ 'procedure? (list (-x 'X₀)) -Λ)
               (-λ '(Y₀) (-@ (-@ •₁ (list (-x 'X₀)) -Λ) (list (-x 'Y₀)) -Λ))
               (-@ •₂ (list (-x 'X₀)) -Λ)))
        (define fun (-λ '(X₀) e))
        (define Γ* (Γ+ Γ (-?@ 'equal? e-f fun)
                         (-?@ 'procedure? •₁)
                         (-?@ 'δ-case? •₂)))
        (define clo (-Clo '(X₀) e -ρ⊥ (Γ↓ Γ* ∅)))
        (↦@ (-W clo fun) (list W-x) Γ* κ σ Ξ M loc)))

    (define case-havoc
      (let ([apply-n-args
             (λ ([n : Natural])
               (define hv• (•!))                     
               (define e• (-@ hv• (list (-@ (-x 'F₀) (for/list ([_ n]) (•!)) -Λ)) -Λ))
               (define f• (-λ '(F₀) e•))
               (define Γ* (Γ+ Γ (-?@ 'equal? e-f f•)
                              (-?@ 'procedure? hv•)
                              (-?@ '= (-?@ 'procedure-arity hv•) (-b 1))))
               (define V• (-Clo '(F₀) e• -ρ⊥ (Γ↓ Γ* ∅)))
               (↦@ (-W V• f•) (list W-x) Γ* κ σ Ξ M loc))])
        (match V-x
          [(-Clo xs _ _ _)
           (apply-n-args
            (match xs
              [(-varargs zs _) (+ 1 (length zs))]
              [(? list? xs) (length xs)]))]
          [(-Ar (-=>i doms rst _ _ _) _ _)
           (apply-n-args (if rst (+ 1 (length doms)) (length doms)))]
          [(or (-St si _) (-St/checked si _ _ _)) #:when si
           (define • (•!))
           (for/fold ([δςs : (Setof -Δς) ∅])
                     ([i (-struct-info-arity si)])
             (define ac (-st-ac si i))
             (define e• (-@ • (list (-@ ac (list (-x 'S₀)) -Λ)) -Λ))
             (define f• (-λ '(S₀) e•))
             (define Γ* (Γ+ Γ (-?@ 'equal? e-f f•)))
             (define V• (-Clo '(S₀) e• -ρ⊥ (Γ↓ Γ* ∅)))
             (define res (↦@ (-W V• f•) (list W-x) Γ* κ σ Ξ M loc))
             (if (set? res) (∪ res δςs) (set-add δςs res)))]
          [_ ∅])))

    (merge case-const case-dep case-havoc))
  
  (match W-xs
    ;; Pure 0-arg function must be constant
    [(list)
     (define res (•!))
     (define Γ* (Γ+ Γ (-?@ 'equal? e-f (-λ '() res))))
     (-Δς (-W -●/Vs res) Γ* κ '() '() '())]
    ;; Defer
    [(list W-x) (↦opq/ce₁ W-x)]
    ;; Non-deterministically pick 1 arg to havoc, and remember choice
    [_
     (define f• (•!))
     (define n (length W-xs))
     (define xs
       (build-list n (λ ([i : Integer]) (string->symbol (format "X~a" (n-sub i))))))
     (for/fold ([reses : (Setof -Δς) ∅])
               ([(W-x i) (in-indexed W-xs)]
                [x-i (in-list xs)])
       (define loc (-src-loc 'havoc (next-loc!)))
       (define body (-@ f• (list x-i) loc))
       (define fun (-λ xs body))
       (define clo (-Clo xs body -ρ⊥ -Γ⊤))
       (define Γ* (Γ+ Γ (-?@ 'equal? e-f fun)))
       (define ans (↦@ (-W clo fun) (list W-x) Γ* κ σ Ξ M loc))
       (if (set? ans) (∪ ans reses) (set-add reses ans)))]))

(define-parameter ↦opq : (-?e (Listof -WV) -?e -Γ -κ -σ -Ξ -M -src-loc → -Δς*) ↦opq/verify)

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
      (define (blm)
        (-Δς (-blm l 'Λ (-Arity-Includes/C n) (list V_f)) Γ κ '() '() '()))
      (cond
        [a =>
         (λ (a)
           (cond [(arity-includes? a n) e ...]
                 [else (blm)]))]
        [else
         (case (Γ⊢e Γ (-?@ 'arity-includes? (-?@ 'procedure-arity e_f) (-b n)))
           [(✓) e ...]
           [(X) (blm)]
           [(?)
            (define ans (begin e ...))
            (if (set? ans) (set-add ans (blm)) {set ans (blm)})])])))

  (: ↦β : -formals -e -ρ -Γ → -Δς*)
  (define (↦β xs e ρ_f Γ_f)
    (define-values (δσ ρ*) (alloc Γ ρ_f xs V_xs pos))
    (define τ (-τ e ρ* Γ_f))
    (define κ* (-kont (-φ.rt.@ Γ xs e_f e_xs) κ))
    (define δΞ (list (cons τ κ*)))
    (-Δς (-⇓ e ρ*) Γ_f τ δσ δΞ '()))

  (: ↦δ : Symbol → -Δς*)
  (define (↦δ o)
    (define-values (δσ AΓ) (δ M σ Γ o W_xs loc))
    (match/nd: (-AΓ → -Δς) AΓ
      [(-AΓ (? -blm? blm) Γ*) (-Δς blm         Γ* κ δσ '() '())]
      [(-AΓ (? list? Vs ) Γ*) (-Δς (-W Vs e_a) Γ* κ δσ '() '())]))
  
  (: ↦indy : (Listof (List Symbol -WV -WV))
              (Option (List Symbol -WV (Listof -WV)))
              -e -ρ -Γ -WV Mon-Info → -Δς*)
  (define (↦indy args Rst d ρ_d Γ_d W_g l³)
    ; Initial parameters and arguments
    (define-values (xs₀ e_xs₀)
      (for/lists ([xs₀ : (Listof Symbol)] [e_xs₀ : (Listof -?e)])
                 ([arg : (List Symbol -WV -WV) args])
        (match-define (list x _ (-W _ e)) arg)
        (values x e)))
    ; Parameters and arguments
    (define-values (xs e_xs)
      (match Rst
        [(list x* _ WVs) (values (-varargs xs₀ x*) (append e_xs₀ (map (inst -W-e Any) WVs)))]
        [#f (values xs₀ e_xs₀)]))
    
    (define κ₁ (-kont (-φ.rt.@ Γ xs e_f e_xs) κ))
    ;; Convert caller's invariants to callee's invariants
    (define Γ_d*
      (let-values ([(xs* e_xs*) (bind-args xs e_xs)])
        (define convert
          (e/map
           (for/hash : (HashTable -e -e) ([x xs*] [e e_xs*] #:when e)
             (values e (-x x)))))
        (define params (list->set xs*))
        (define φs-caller (-Γ-facts Γ))
        (define φs-callee
          (for*/set: : (Setof -e) ([φ φs-caller]
                                   [FV-φ (in-value (FV φ))]
                                   #:when (set-empty? (∩ FV-φ params))
                                   #:when (or (opq-exp? φ) (not (set-empty? FV-φ))) ; prevents blow-up
                                   [φ* (in-value (convert φ))]
                                   #:when (⊆ (FV φ*) params))
            φ*))
        ; Canonicalize propositions if needed
        (define Γ_d₀
          (for/fold ([Γ : -Γ Γ_d]) ([x xs*]
                                    [e_x e_xs*]
                                    #:when e_x
                                    #:when (⊆ (FV e_x) params))
            (Γ-bind Γ x e_x)))
        (define φs-callee* (map/set (curry canonicalize Γ_d₀) φs-callee))
        (Γ⊓ Γ_d₀ φs-callee*)))

    #|(printf "Binding ~a~n" (for/list : (Listof Any) ([x xs₀] [e e_xs₀])
                             `(,(show-e x) ↦ ,(show-?e e))))
    (printf "Caller knows: ~a~n" (show-Γ Γ))
    (printf "Callee knows: ~a~n" (show-Γ Γ_d))
    (printf "Starting argument, knowing ~a~n" (and Γ_d* (show-Γ Γ_d*)))|#
    
    (cond
      [Γ_d*
       (match args
         ['()
          (match Rst
            [(list x* W_c* W_vs)
             (define-values (Vs es) ((inst unzip-by -WV -V -?e) -W-x -W-e W_vs))
             (define-values (δσ V-rst) (alloc-varargs Γ Vs pos))
             (define e-rst (-?list es))
             (define κ₂ (-kont (-φ.indy.rst x* '() W_g d ρ_d l³ pos) κ₁))
             (define l³* (swap-parties l³))
             (with-Δ δσ '() '()
               (↦mon W_c* (-W V-rst e-rst) Γ κ₂ σ Ξ M l³* pos))]
            [#f
             ;; If there's no argument, skip monitoring arguments and start evaluating range
             (define κ₂ (-kont (-φ.indy.rng W_g '() #f l³ pos) κ₁))
             (-Δς (-⇓ d ρ_d) Γ_d* κ₂ '() '() '())])]
         [(cons (list x W_c (-W V_x e_x)) args*)
          (define l³* (swap-parties l³))
          (cond
            [Γ_d*
             (define W_x* (-W V_x (canonicalize Γ_d* (-x x))))
             (define κ₂ (-kont (-φ.indy.dom x args* '() Rst W_g d ρ_d l³ pos) κ₁))
             (↦mon W_c W_x* Γ_d* κ₂ σ Ξ M l³* pos)]
            [else ∅])])]
      [else ∅]))

  (: ↦pred : -struct-info → -Δς)
  (define (↦pred si)
    (case (MσΓ⊢oW M σ Γ (-st-p si) (car W_xs))
      [(✓) (-Δς (-W (list -tt) e_a) (Γ+ Γ e_a) κ '() '() '())]
      [(X) (-Δς (-W (list -ff) e_a) (Γ+ Γ (-not e_a)) κ '() '() '())]
      [(?) (-Δς (-W -●/Vs e_a) Γ κ '() '() '())]))

  (: ↦con : -struct-info → -Δς)
  (define (↦con si)
    (define αs (alloc-fields si e_xs pos))
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
        [(-Vector/checked γs _ _) (-b (length γs))]
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
                 (case (MσΓ⊢oW M σ Γ-ok '= W-idx (-W (-b i) (-b i)))
                   [(X) acc]
                   [else
                    (define Γ* (Γ+ Γ-ok (-?@ '= e-idx (-b i))))
                    (for/fold ([acc : (Setof -Δς) acc]) ([V (σ@ σ α)])
                      (set-add acc (-Δς (-W (list V) e_a) Γ* κ '() '() '())))]))])]
           [(-Vector/checked γs l³ α)
            (define φ-ref
              (-φ.@ (list (-W (list V-idx) e-idx)) (list -vector-ref/W)
                    (-src-loc (first l³) pos)))
            (for*/fold ([acc : (Setof -Δς) ∅])
                       ([V (σ@ σ α)]
                        [(γ i) (in-indexed γs)])
              (case (MσΓ⊢oW M σ Γ-ok '= W-idx (-W (-b i) (-b i)))
                [(X) acc]
                [else
                 (define Γ* (Γ+ Γ-ok (-?@ '= e-idx (-b i))))
                 (for/fold ([acc : (Setof -Δς) acc]) ([C (σ@ σ γ)])
                   (define φ-mon (-φ.mon.v (-W C #f #|TODO|#) l³ pos))
                   (define κ* (-kont* φ-ref φ-mon κ))
                   (set-add acc (-Δς (-W (list V) e-vec) Γ* κ* '() '() '())))]))]
           [(-Vector/same γ l³ α)
            (define φ-ref
              (-φ.@ (list (-W (list V-idx) e-idx)) (list -vector-ref/W)
                    (-src-loc (first l³) pos)))
            (for*/set: : (Setof -Δς)
                       ([C (σ@ σ γ)]
                        [φ-mon (in-value (-φ.mon.v (-W C #f #|TODO|#) l³ pos))]
                        [κ* (in-value (-kont* φ-ref φ-mon κ))]
                        [V (σ@ σ α)])
              (-Δς (-W (list V) e-vec) Γ κ* '() '() '()))]
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
              (define φ-set
              (-φ.@ '() (list W-idx (-W V e-vec) -vector-set/W)
                    (-src-loc (first l³) pos)))
              (define φ-mon (-φ.mon.v (-W C #f #|TODO|#) l³ pos))
              (define κ* (-kont* φ-mon φ-set κ))
              (-Δς (-W (list V-val) e-val) Γ-ok κ* '() '() '()))]
           [(-Vector/same γ l³ α)
            (for*/set: : (Setof -Δς)
                       ([C (σ@ σ γ)]
                        [φ-mon (in-value (-φ.mon.v (-W C #f #|TODO|#) l³ pos))]
                        [V (σ@ σ α)]
                        [φ-set
                         (in-value
                          (-φ.@ '() (list W-idx (-W V e-vec) -vector-set/W)
                                (-src-loc (first l³) pos)))]
                        [κ* (in-value (-kont* φ-mon φ-set κ))])
              (-Δς (-W (list V-val) e-val) Γ κ* '() '() '()))]
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

  (: ↦struct/c : -struct-info (Setof (Listof -V)) → -Δς*)
  (define (↦struct/c si field-lists)
    (match-define (list (-W V_x e_x)) W_xs)
    (define φ₀
      (let ([p? (-st-p si)])
        (-φ.@ '() (list (-W p? p?)) loc)))
    (define cs (-struct/c-split e_f (-struct-info-arity si)))
    (define vs (-struct-split e_x si))
    (match/nd: ((Listof -V) → -Δς) field-lists
      [Cs
       (define W_cs (map (inst -W -V) Cs cs))
       (match V_x
         [(-St (≡ si) αs)
          (for/set: : (Setof -Δς) ([Vs (σ@/list σ αs)])
            (define W_vs (map (inst -W -V) Vs vs))
            (define κ*
              (foldr (λ ([W_c : -WV] [W_v : -WV] [κ : -κ])
                       (define φ (-φ.if (-App W_c (list W_v) loc) (-W (list -ff) -ff)))
                       (-kont φ κ))
                     κ
                     W_cs
                     W_vs))
            (-Δς (-W (list V_x) e_x) Γ (-kont φ₀ κ*) '() '() '()))]
         [(-●) (-Δς (-W -●/Vs e_a) Γ κ '() '() '())]
         [_ (-Δς (-W (list -ff) e_a) Γ κ '() '() '())])]))
  
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
      [(-=>i Doms Rst _ _ _) ; check arity
       (cond
         [(-procedure-arity V) =>
          (λ ([ar : Arity])
            (define target-arity
              (let ([n (length Doms)])
                (if Rst (arity-at-least n) n)))
            (define ans
              (cond
                [(arity-includes? ar target-arity) (-W (list -tt) -tt)]
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
    [(-St/C #t si αs) (with-guarded-arity (↦struct/c si (σ@/list σ αs)))]
    [(? symbol? o) (↦δ o)]
    [(-Clo* xs e ρ_f    ) (with-guarded-arity (↦β xs e ρ_f (Γ↓ Γ (dom ρ_f))))]
    [(-Clo  xs e ρ_f Γ_f) (with-guarded-arity (↦β xs e ρ_f Γ_f))]
    [(-Ar (-=>i Doms Rst d ρ_c Γ_c) (cons α e_g) l³)
     (define-values (xs cs γs)
       (for/lists ([xs : (Listof Symbol)] [cs : (Listof -?e)] [γs : (Listof -α)])
                  ([Dom : (Pairof Symbol -α.dom) Doms])
         (match-define (cons x (and γ (-α.dom c))) Dom)
         (values x (and (-e? c) c) γ)))
     (match/nd: ((Listof -V) → -Δς) (σ@/list σ γs) ; TODO can explode very fast!!
       [Cs
        (define WCs (map (inst -W -V) Cs cs))
        (match/nd: (-V → -Δς) (σ@ σ α)
          [V_g
           (with-guarded-arity
             (match Rst
               [(cons x* (and γ* (-α.rst c*)))
                (define n (length Doms))
                (define-values (es-init es-rest) (split-at e_xs n))
                (define-values (Vs-init Vs-rest) (split-at V_xs n))
                (define args-init
                  (for/list : (Listof (List Symbol -WV -WV))
                            ([x xs] [c cs] [C Cs] [V Vs-init] [e es-init])
                    (list x (-W C c) (-W V e))))
                (define WV-rest (map (inst -W -V) Vs-rest es-rest))
                (match/nd: (-V → -Δς) (σ@ σ γ*)
                  [C*
                   (define Rst* (list x* (-W C* (and (-e? c*) c*)) WV-rest))
                   (↦indy args-init Rst* d ρ_c Γ_c (-W V_g e_g) l³)])]
               [#f
                (define args
                  (for/list : (Listof (List Symbol -WV -WV))
                            ([x xs] [c cs] [C Cs] [V V_xs] [e e_xs])
                    (list x (-W C c) (-W V e))))
                (↦indy args #f d ρ_c Γ_c (-W V_g e_g) l³)]))])])]
    [(-●)
     (with-guarded-arity
       (cond
         [(concretized? Γ e_f) =>
          (match-lambda
            [(and vf (-λ xs e))
             (define Vf (-Clo xs e -ρ⊥ (Γ↓ Γ ∅)))
             (↦@ (-W Vf vf) W_xs Γ κ σ Ξ M loc)])]
         [(equal? '✓ (Γ⊢e Γ (-?@ 'δ-case? e_f)))
          (-Δς (-W -●/Vs e_a) Γ κ '() '() '())]
         [else ((↦opq) e_f W_xs e_a Γ κ σ Ξ M loc)]))]
    [_ (-Δς (-blm l 'apply 'procedure? (list V_f)) Γ κ '() '() '())]))

(: rt-strengthen ([-M -σ -φ.rt.@ -Γ] [-WVs] . ->* . (Option -Γ)))
;; Compute a strengthened path invariant on return, or `#f` if it's spurious
(define (rt-strengthen M σ φ Γ [W (-W '() #f)])
  (match-define (-W Vs ?e) W)
  (match-define (-φ.rt.@ Γ₀ xs* e_f e_xs*) φ)
  (define-values (xs e_xs) (bind-args xs* e_xs*))
  
  (define params ; only care params that have corresponding args
    (for/set: : (Setof Symbol) ([x xs] [e_x e_xs] #:when e_x) x))

  (define ans_caller (apply -?@ e_f e_xs))

  ; Function for converting invariants about parameters in callee's environment
  ; into invariants about arguments in caller's environment
  ; PRECOND: FV⟦e⟧ ⊆ xs
  (define convert
    (e/map
     (let ([m (for/hash : (HashTable -e -e) ([x xs] [e_x e_xs] #:when e_x)
                (values (-x x) e_x))])
       (if (and ?e ans_caller (not (closed? ?e)))
           (hash-set m ?e ans_caller)
           m))))

  (define facts-from-callee
    (for/set: : -es ([e (-Γ-facts Γ)] #:when (⊆ (FV e) params))
      (convert e)))

  ; Check if the propositions would contradict
  (define Γ₀* (MσΓ⊓ M σ Γ₀ facts-from-callee))

  (begin ;; debug
    (dbg 'rt "Return from: ~a~n"
         `(,(show-?e e_f)
           ,@(for/list : (Listof Sexp) ([x xs] [e_x e_xs])
               `(,x ↦ ,(show-?e e_x)))))
    (dbg 'rt "Caller knows: ~a~n" (show-Γ Γ₀))
    (dbg 'rt "Callee knows: ~a~n" (show-Γ Γ))
    (dbg 'rt "Caller would know: ~a~n~n" (and Γ₀* (show-Γ Γ₀*))))

  (cond
    [(and Γ₀* (not (spurious? M σ Γ₀* (-W Vs (and ?e (convert ?e))))))
     Γ₀*]
    [else #f]))
