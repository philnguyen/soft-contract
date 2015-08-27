#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt" "delta.rkt" "machine.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(provide ↦ ↦* dbg)

(: ↦ : -ς → -ς*)
;; Steps a full state in the CEΓKSΞ machine
(define ↦
  (match-lambda
    [(-ς (-↓ e ρ) Γ τ σ Ξ M) (↦e e ρ Γ τ σ Ξ M)]
    [(-ς (-Mon C V l³) Γ τ σ Ξ M)
     (↦mon (-W C #f) (-W V #f) Γ τ σ Ξ M l³)]
    [(-ς (-FC C V l) Γ τ σ Ξ M)
     (↦FC C V Γ τ σ Ξ M l)]
    [(-ς (? -W? W) Γ τ σ Ξ M)
     (match/nd: (-κ → -ς) (hash-ref Ξ τ)
       [(-κ φ τ*) (↦WVs W Γ φ τ* σ Ξ M)])]
    [(-ς (? -blm? blm) Γ τ σ Ξ M)
     (match/nd: (-κ → -ς) (hash-ref Ξ τ)
       [(-κ φ τ*) (↦blm blm Γ φ τ* σ Ξ M)])]
    [ς (error '↦ "unexpected: ~a" ς)]))

(: ↦e : -e -ρ -Γ -τ -σ -Ξ -M → -ς*)
;; Stepping rules for "eval" states
(define (↦e e ρ Γ τ σ Ξ M)
  (match e
    ;; close value
    [(? -v? v)
     (-ς (-W (list (close v ρ Γ)) v) Γ τ σ Ξ M)]
    ;; look up variable
    [(? -x? x)
     (match (ρ@ ρ x)
       ; TODO hack for now
       ['undefined
        (-ς (-blm 'TODO 'undefined 'defined? (list (-b 'undefined))) Γ τ σ Ξ M)]
       [α
        (for*/set: : (Setof -ς) ([V (σ@ σ α)]
                                 [W (in-value (-W (list V) x))]
                                 #:unless (spurious? Γ W))
          (-ς W Γ τ σ Ξ M))])]
    ;; look up top-level reference
    [(and ref (-ref (and id (-id name ctx*)) ctx))
     (cond
       ;; skip contract checking for self reference
       [(equal? ctx ctx*)
        (for/set: : (Setof -ς) ([V (σ@ σ (-α.def id))])
          (-ς (-W (list V) ref) Γ τ σ Ξ M))]
       ;; perform contract checking for cross-module reference
       [else
        ;; FIXME
        (define Vs (σ@ σ (-α.def id)))
        (define Cs (σ@ σ (-α.ctc id)))
        (match/nd: #:tag ↦e/ref/V (-V → -ς) Vs
          [V (match/nd: #:tag ↦e/ref/C (-V → -ς) Cs
               [C (↦mon (-W C #f) (-W V ref) Γ τ σ Ξ M (list ctx* ctx ctx*))])])])]
    ;; evaluate function position, pushing arguments
    [(-@ f xs l)
     (define φ (-φ.@ (for/list : (Listof -E) ([x xs]) (-⇓ x ρ)) '() l))
     (-ς/pushed f ρ Γ φ τ σ Ξ M)]
    ;; evaluate scrutiny, pushing branches
    [(-if e₀ e₁ e₂)
     (define φ (-φ.if (-⇓ e₁ ρ) (-⇓ e₂ ρ)))
     (-ς/pushed e₀ ρ Γ φ τ σ Ξ M)]
    ;; ignore continuation marks for now
    [(-wcm e_k e_v e_b)
     (error '↦e "TODO: wcm")]
    ;; evaluate first clause in `begin0` and push the remaining clauses
    [(-begin0 e₀ es)
     (cond
       [(null? es) (-ς (-↓ e₀ ρ) Γ τ σ Ξ M)]
       [else
        (define φ (-φ.begin0v es ρ))
        (-ς/pushed e₀ ρ Γ φ τ σ Ξ M)])]
    ;; quote
    [(-quote x)
     (error '↦e "TODO: quote")]
    ;; let-values: evaluate the first argument (if there is) and push the rest
    [(-let-values bnds e* l)
     (match bnds
       ['() (-ς (-↓ e* ρ) Γ τ σ Ξ M)]
       [(cons (cons xs eₓ) bnds*)
        (define φ (-φ.let-values xs bnds* (hash) ρ e* l))
        (-ς/pushed eₓ ρ Γ φ τ σ Ξ M)])]
    ;; letrec-values
    [(-letrec-values bnds e l)
     (match bnds
       ['() (-ς (-↓ e ρ) Γ τ σ Ξ M)]
       [(cons (cons xs e*) bnds*)
        (define ρ*
          (for*/fold ([ρ* : -ρ ρ]) ([bnd bnds] [x (in-list (car bnd))])
            (ρ+ ρ* x 'undefined)))
        (define φ (-φ.letrec-values xs bnds* ρ* e l (dom ρ)))
        (-ς/pushed e* ρ* Γ φ τ σ Ξ M)])]
    [(-set! x e*)
     (define φ (-φ.set! (ρ@ ρ x)))
     (-ς/pushed e* ρ Γ φ τ σ Ξ M)]
    ;; @-havoc
    [(-@-havoc x)
     (match/nd: #:tag ↦WVs/havoc/x (-V → -ς) (σ@ σ (ρ@ ρ x))
       [(and V (-Clo xs _ ρ Γ))
        (define n
          (match xs
            [(? list?) (length xs)]
            [(-varargs zs _) (+ 1 (length zs))]))
        (↦@ (-W V #f) (make-list n -●) Γ τ σ Ξ M ☠)]
       [(and V (-Ar γ _ l³))
        (match/nd: #:tag ↦WVs/havoc/dep (-V → -ς) (σ@ σ γ)
          [(-=>i cs _ _ _) (↦@ (-W V #f) (make-list (length cs) -●) Γ τ σ Ξ M ☠)])]
       [V
        (log-debug "havoc: ignore first-order value ~a" (show-V σ V))
        ∅])]
    ;; amb
    [(-amb es)
     (for/set: : (Setof -ς) ([e es])
       (-ς (-⇓ e ρ) Γ τ σ Ξ M))]
    ;; contract stuff
    [(-μ/c x c)
     (error '↦e "TODO: μ/c")]
    [(-->i doms rng)
     (match doms
       ['()
        (define φ (-φ.=>i '() '() '() rng ρ))
        (-ς/pushed rng ρ Γ φ τ σ Ξ M)]
       [(cons dom doms*)
        (match-define (cons x c) dom)
        (define-values (xs* cs*)
          (for/lists ([xs* : (Listof Symbol)] [cs* : (Listof -e)])
                     ([dom doms*])
            (values (car dom) (cdr dom))))
        (define φ (-φ.=>i cs* '() (cons x xs*) rng ρ))
        (-ς/pushed c ρ Γ φ τ σ Ξ M)])]
    [(-x/c x)
     (error '↦e "TODO: x/c")]
    [(-struct/c id cs)
     (match cs
       ['() (-ς (-W (list (-St/C id '())) #f) Γ τ σ Ξ M)]
       [(cons c cs*)
        (define φ (-φ.struct/c id cs* ρ '()))
        (-ς/pushed c ρ Γ φ τ σ Ξ M)])]
    ))

(: ↦WVs : -WVs -Γ -φ -τ -σ -Ξ -M → -ς*)
;; Stepping rules for "apply" states
(define (↦WVs W Γ φ τ σ Ξ M)
  (match-define (-W Vs ?e) W)
  ;; Leave `M` alone for now. TODO: update it.

  (define-syntax-rule (with-guarded-arity n l+ lo e ...)
    (let ([n* n])
      (cond
        [(= n (length Vs)) e ...]
        [else
         (-ς (-blm l+ lo
                   (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) 'Λ) -ρ∅ -Γ∅)
                   Vs)
             Γ τ σ Ξ M)])))
  
  (match φ
    ;; Conditional
    [(-φ.if E₁ E₂)
     (match Vs
       [(list V)
        (define-values (Γ_t Γ_f) (Γ+/-W Γ (-W V ?e)))
        (define ς_t (and Γ_t (-ς E₁ Γ_t τ σ Ξ M)))
        (define ς_f (and Γ_f (-ς E₂ Γ_f τ σ Ξ M)))
        (cond
          [(and ς_t ς_f) {set ς_t ς_f}]
          [ς_t ς_t]
          [ς_f ς_f]
          [else (error '↦WVs "both if branches are bogus (!)")])]
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
          (define-values (ρ* Γ* σ*)
            (for/fold ([ρ* : -ρ ρ] [Γ* : -Γ Γ] [σ* : -σ σ])
                      ([(x W) (in-hash bnds↓*)])
              (match-define (-W V ex) W)
              (define α (-α.bnd x ex Γ))
              (values (ρ+ ρ* x α)
                      (Γ+ Γ* (-?@ 'equal? (-x x) ex))
                      (⊔ σ* α V))))
          (define φ* (-φ.rt.let (dom ρ)))
          (-ς/pushed e ρ* Γ* φ* τ σ* Ξ M)]
         ;; Proceed to next assigning clause
         [(cons (cons xs* e*) bnds*)
          (define φ* (-φ.let-values xs* bnds* bnds↓* ρ e l))
          (-ς/pushed e* ρ Γ φ* τ σ Ξ M)]))]
    ;; letrec-values
    [(-φ.letrec-values xs bnds ρ e l dom₀)
     (define n (length xs))
     (with-guarded-arity n l 'letrec-values
       (define-values (ρ* Γ* σ*)
         (for/fold ([ρ* : -ρ ρ] [Γ* : -Γ Γ] [σ* : -σ σ])
                   ([x xs] [V Vs] [ex (split-values ?e n)])
           (define α (-α.bnd x ?e Γ))
           (values (ρ+ ρ* x α)
                   (Γ+ Γ* (-?@ 'equal? (-x x) ex))
                   (⊔ σ* α V))))
       (match bnds
         ;; proceed to letrec's body
         ['()
          (define φ* (-φ.rt.let dom₀))
          (-ς/pushed e ρ* Γ* φ* τ σ* Ξ M)]
         ;; proceed to next assigning clause
         [(cons (cons xs* e*) bnds*)
          (define φ* (-φ.letrec-values xs* bnds* ρ e l dom₀))
          (-ς/pushed e* ρ* Γ* φ* τ σ* Ξ M)]))]
    [(-φ.set! α)
     (with-guarded-arity 1 'TODO 'set!
       (define Γ* #|FIXME update!!|# Γ)
       (define σ* (⊔ σ α (first Vs)))
       (-ς (-W -Void/Vs #f) Γ* τ σ Ξ M))]
    ;; Application
    [(-φ.@ Es WVs l)
     (with-guarded-arity 1 l 'apply
       (match-define (list V) Vs)
       (define WVs* (cons (-W V ?e) WVs))
        (match Es
          ['()
           (match-define (cons W_f W_xs) (reverse WVs*))
           (↦@ W_f W_xs Γ τ σ Ξ M l)]
          ;; Swap next argument for evaluation
          [(cons E* Es*)
           (define φ* (-φ.@ Es* WVs* l))
           (-ς/pushed E* Γ φ* τ σ Ξ M)]))]
    ;; Begin
    [(-φ.begin es ρ)
     (match es
       [(list) (-ς (-W -Void/Vs -void) Γ τ σ Ξ M)]
       [(list e) (-ς (-↓ e ρ) Γ τ σ Ξ M)]
       [(cons e es*)
        (define φ* (-φ.begin es* ρ))
        (-ς/pushed e ρ Γ φ* τ σ Ξ M)])]
    ;; begin0
    ; waiting on first clause
    [(-φ.begin0v es ρ)
     (match es
       ['() (-ς W Γ τ σ Ξ M)]
       [(cons e es*)
        (define φ* (-φ.begin0e W es* ρ))
        (-ς/pushed e ρ Γ φ* τ σ Ξ M)])]
    ; waiting on next clause (and discard)
    [(-φ.begin0e W es ρ)
     (match es
       ['() (-ς W Γ τ σ Ξ M)]
       [(cons e es*)
        (define φ* (-φ.begin0e W es* ρ))
        (-ς/pushed e ρ Γ φ* τ σ Ξ M)])]
    ;; mon
    ; waiting on the contract
    [(-φ.mon.c E (and l³ (list _ _ lo)))
     (with-guarded-arity 1 lo 'Λ
       (match-define (list C) Vs)
       (define W_C (-W C ?e))
       (cond
         [(-WV? E) (↦mon W_C E Γ τ σ Ξ M l³)]
         [else
          (define φ* (-φ.mon.v W_C l³))
          (-ς/pushed E Γ φ* τ σ Ξ M)]))]
    ; waiting on the value to be checked
    [(-φ.mon.v C (and l³ (list l+ _ lo)))
     (with-guarded-arity 1 l+ lo
       (match-define (list V) Vs)
       (define W_V (-W V ?e))
       (cond
         [(-WV? C) (↦mon C W_V Γ τ σ Ξ M l³)]
         [else
          (define φ* (-φ.mon.c W_V l³))
          (-ς/pushed C Γ φ* τ σ Ξ M)]))]
    ;; indy
    #;[(-φ.indy W_cs W_xs W_xs↓ rng (list l+ l- lo))
     (with-guarded-arity 1 l+ lo
       (error '↦WVs "TODO: indy"))]
    ;; restore fact environment
    [(-φ.rt.@ Γ₀ xs e_f e_xs)
     (cond [(rt-spurious? φ Γ (-W Vs ?e)) ∅]
           [else
            (define e_a (apply -?@ e_f e_xs))
            (-ς (-W Vs e_a) Γ₀ τ σ Ξ M)])]
    ;; contract stuff
    [(-φ.μc x)
     (match Vs
       [(list V) (error '↦WVs "TODO: μ/c")]
       [_ (error '↦WVs "TODO: catch arity error for μ/c")])]
    [(-φ.struct/c id es ρ WVs)
     (match Vs
       [(list V)
        (define WVs* (cons (-W V ?e) WVs))
        (match es
          ['()
           (define n (length WVs*))
           (define-values (αs σ* es*)
             ; accumulate new store and address list
             ; which is reversed compard to `WVs*`, hence of the right order
             (for/fold ([αs : (Listof -α) '()] [σ* : -σ σ] [es* : (Listof -?e) '()])
                       ([WV WVs*] [i (in-range n)])
               (match-define (-W V e) WV)
               (define α
                 (cond [e (-α.val e)]
                       [else (-α.opq (id/c id) #f #|FIXME|# i)]))
               (values (cons α αs)
                       (⊔ σ* α V)
                       (cons e es*))))
           (define C (-St/C id αs))
           (define e_C (-?struct/c id es*))
           (-ς (-W (list C) e_C) Γ τ σ* Ξ M)]
          [(cons e es*)
           (define φ* (-φ.struct/c id es* ρ WVs*))
           (-ς/pushed e ρ Γ φ* τ σ Ξ M)])]
       [else (error '↦WVs "TODO: catch arity error for μ/c")])]
    [(-φ.=>i doms doms↓ xs rng ρ)
     (match Vs
       [(list V)
        (define doms↓* (cons (-W V ?e) doms↓))
        (define n (length doms↓*))
        (match doms
          ['()
           (define-values (αs σ* es*)
             ;; accumulate new store and address list for contract domains
             ;; (domains are reversed compared to `cs↓*`)
             (for/fold ([αs : (Listof -α) '()] [σ* : -σ σ] [es* : (Listof -?e) '()])
                       ([dom doms↓*] [i (in-range n)])
               (match-define (-W C e) dom)
               (define α
                 (cond [e (-α.val e)]
                       [else (-α.opq (-id '->/i 'Λ) #f #|TODO|# i)]))
               (values (cons α αs)
                       (⊔ σ* α V)
                       (cons e es*))))
           (define C (-=>i (map (inst cons Symbol -α) xs αs) rng ρ Γ))
           (define e_C (-?->i xs es* rng))
           (-ς (-W (list C) e_C) Γ τ σ* Ξ M)]
          [(cons dom doms*)
           (define φ* (-φ.=>i doms* doms↓* xs rng ρ))
           (-ς/pushed dom ρ Γ φ* τ σ Ξ M)])]
       [else (error '↦WVs "TODO: catch arity error for -->i")])]
    ))

(: ↦blm : -blm -Γ -φ -τ -σ -Ξ -M → -ς*)
;; Either propagate error or eliminate a spurious one
(define (↦blm blm Γ φ τ σ Ξ M)
  (match φ
    [(-φ.rt.@ Γ₀ _ _ _)
     (cond [(rt-spurious? φ Γ) ∅]
           [else (-ς blm Γ₀ τ σ Ξ M)])]
    [(-φ.rt.let dom) (-ς blm (Γ↓ Γ dom) τ σ Ξ M)]
    [_ (-ς blm Γ τ σ Ξ M)]))

(: ↦@ : -WV (Listof -WV) -Γ -τ -σ -Ξ -M Mon-Party → -ς*)
;; Stepping rules for function application
(define (↦@ W_f W_xs Γ τ σ Ξ M l)

  (: ↦indy : -=>i -V (Listof -V) Mon-Info → -ς*)
  (define (↦indy C V_f V_xs l³)
    (match-define (list l+ l- lo) l³)
    (match C
      [(-=>i doms rng ρ_c Γ_c)
       (error '↦indy "TODO: indy")]))
  
  (match-define (-W V_f e_f) W_f)
  (define-values (V_xs e_xs)
    (for/lists ([V_xs : (Listof -V)] [e_xs : (Listof -?e)]) ([W W_xs])
      (values (-W-x W) (-W-e W))))
  (define e_a (apply -?@ e_f e_xs))
  (match V_f
    [(? -o? o)
     (define-values (σ* AΓs) (δ σ Γ o W_xs l))
     (match/nd: (-AΓ → -ς) AΓs
       [(-AΓ (? -blm? blm) Γ*) (-ς blm Γ* τ σ* Ξ M)]
       [(-AΓ (? list? Vs ) Γ*) (-ς (-W Vs e_a) Γ* τ σ* Ξ M)])]
    [(-Clo xs e ρ_f Γ_f)
     (match xs
       [(? list? xs)
        (define-values (ρ* σ*)
          (for/fold ([ρ* : -ρ ρ_f] [σ* : -σ σ])
                    ([x xs] [V_x V_xs] [ex e_xs])
            (define α (-α.bnd x ex (if ex (Γ↓ Γ (FV ex)) -Γ∅)))
            (values (ρ+ ρ* x α) (⊔ σ* α V_x))))
        (define φ* (-φ.rt.@ Γ xs e_f e_xs))
        (-ς/pushed e ρ* Γ_f φ* τ σ* Ξ M)]
       [(-varargs zs z) (error '↦@ "TODO: varargs")])]
    [(-Ar γ α l³)
     (define Cs (σ@ σ γ))
     (define Vs (σ@ σ α))
     (match/nd: (-V → -ς) Cs
       [(? -=>i? C)
        (match/nd: (-V → -ς) Vs
          [V_g (↦indy C V_g V_xs l³)])])]
    ['•
     (define V_havoc (σ@₁ σ (-α.def havoc-id)))
     (define W_havoc (-W V_havoc (-ref havoc-id l)))
     ;; FIXME: return right arity!
     (define ς• (-ς (-W (list '•) e_a) Γ τ σ Ξ M)) 
     (for/fold ([acc : (Setof -ς) {set ς•}])
               ([W_x W_xs])
       (match (↦@ W_havoc (list W_x) Γ τ σ Ξ M 'Λ)
         [(? set? s) (set-union acc s)]
         [(? -ς? ς) (set-add acc ς)]))]
    [_ (-ς (-blm l 'apply 'procedure? (list V_f)) Γ τ σ Ξ M)]))

(: ↦mon : -WV -WV -Γ -τ -σ -Ξ -M Mon-Info → -ς*)
;; Stepping rules for contract monitoring
(define (↦mon W_c W_v Γ τ σ Ξ M l³)
  (match-define (-W C e_c) W_c)
  (match-define (-W V e_v) W_v)
  (match-define (list l+ l- lo) l³)

  (match (Γ⊢V∈C Γ W_v W_c)
    ['✓
     (define Γ* (Γ+ Γ (-?@ e_c e_v)))
     (-ς (-W (list V) e_v) Γ* τ σ Ξ M)]
    ['X
     (define Γ* (Γ+ Γ (-not (-?@ e_c e_v))))
     (-ς (-blm l+ lo C (list V)) Γ* τ σ Ξ M)]
    ['?
     (match C
       [(-=>i doms rng ρ_c Γ_c)
        ;; TODO: check for arity also
        (define-values (Γ-ok Γ-bad) (Γ+/-W∈W Γ W_v (-W 'procedure? 'procedure?)))
        (define ς-ok
          (and Γ-ok
               (let ()
                 (define γ
                   (cond [e_c (-α.val e_c)]
                         [else (-α.opq (-id 'Ar 'Λ) #f #|FIXME|# 0)]))
                 (define α
                   (cond [e_v (-α.val e_v)]
                         [else (-α.opq (-id 'Ar 'Λ) #f #|FIXME|# 1)]))
                 (define Ar (-Ar γ α l³))
                 (define σ* (⊔ (⊔ σ α V) γ C))
                 (-ς (-W (list Ar) #f) Γ-ok τ σ* Ξ M))))
        (define ς-bad
          (and Γ-bad
               (-ς (-blm l+ lo 'procedure? (list V)) Γ-bad τ σ Ξ M)))
        (cond
          [(and ς-ok ς-bad) {set ς-ok ς-bad}]
          [ς-ok ς-ok]
          [ς-bad ς-bad]
          [else (error '↦mon "impossible")])]
       [(-St/C id cs)
        (error '↦mon "struct/c")]
       [(-μ/C x c)
        (error '↦mon "μ/c")]
       [(-X/C x)
        (error '↦mon "ref")]
       [(-St (-id 'and/c 'Λ) (list γ₁ γ₂))
        (define Cs₁ (σ@ σ γ₁))
        (define Cs₂ (σ@ σ γ₂))
        (match/nd: (-V → -ς) Cs₁
          [C₁
           (match/nd: (-V → -ς) Cs₂
             [C₂
              ;; TODO: more precise splitting `(and/c _₁ _₂) --> _₁, _₂`
              (define φ* (-φ.mon.v (-W C₂ #f) l³))
              (define τ* (-τ (-Mon C₁ V l³) Γ))
              (define Ξ* (⊔ Ξ τ* (-κ φ* τ)))
              (↦mon (-W C₁ #f) W_v Γ τ* σ Ξ* M l³)])])]
       [(-St (-id 'or/c 'Λ) (list γ₁ γ₂))
        (define Cs₁ (σ@ σ γ₁))
        (define Cs₂ (σ@ σ γ₂))
        (match/nd: (-V → -ς) Cs₁
          [C₁
           (cond
             [(C-flat? σ C₁)
              (match/nd: (-V → -ς) Cs₂
                [C₂
                 (define φ (-φ.if (-Mon C₂ V l³) (-blm l+ lo C₁ (list V))))
                 (define E* (-FC C₁ V lo))
                 (define τ* (-τ E* Γ))
                 (define Ξ* (⊔ Ξ τ* (-κ φ τ)))
                 (-ς E* Γ τ* σ Ξ* M)])]
             [else
              (-ς (-blm lo 'Λ #|hack|# (-st-p (-id 'flat-contract? 'Λ) 1) (list C₁))
                  Γ τ σ Ξ M)])])]
       [(-St (-id 'not/c 'Λ) (list α))
        (match/nd: (-V → -ς) (σ@ σ α)
          [C*
           (cond
             [(C-flat? σ C*)
              (define φ (-φ.if (-blm l+ lo C (list V)) (-W (list V) e_v)))
              (-ς/pushed (-FC C* V lo) Γ φ τ σ Ξ M)]
             [else
              (-ς (-blm lo 'Λ #|hack|# (-st-p (-id 'flat-contract? 'Λ) 1) (list C*))
                  Γ τ σ Ξ M)])])]
       [_
        (define φ* (-φ.if (-W (list V) e_v) (-blm l+ lo C (list V))))
        (define τ* (-τ (list '@ (-W (list C) e_c) (-W (list V) e_v)) Γ))
        (define Ξ* (⊔ Ξ τ* (-κ φ* τ)))
        (↦@ W_c (list W_v) Γ τ* σ Ξ* M lo)])]))

(: ↦FC : -V -V -Γ -τ -σ -Ξ -M Mon-Party → -ς*)
;; Stepping rules for monitoring flat contracts
(define (↦FC C V Γ τ σ Ξ M l)
  (match C
    [(-St (-id (and t (or 'and/c 'or/c)) 'Λ) (list γ₁ γ₂))
     (define Cs₁ (σ@ σ γ₁))
     (define Cs₂ (σ@ σ γ₂))
     (match/nd: (-V → -ς) Cs₁
       [C₁
        (match/nd: (-V → -ς) Cs₂
          [C₂
           (define φ
             (match t
               ['and/c (-φ.if (-FC V C₂ l) (-W (list -ff) -ff))]
               ['or/c  (-φ.if (-W (list -tt) -tt) (-FC V C₂ l))]))
           (-ς/pushed (-FC C₁ V l) Γ φ τ σ Ξ M)])])]
    [(-St (-id 'not/c 'Λ) (list γ))
     (match/nd: (-V → -ς) (σ@ σ γ)
       [C*
        (define φ (-φ.@ '() (list (-W 'not 'not)) 'Λ))
        (-ς/pushed (-FC C* V l) Γ φ τ σ Ξ M)])]
    ;; FIXME recursive contract
    [_ (↦@ (-W C #f) (list (-W V #f)) Γ τ σ Ξ M l)]))

(: -ς/pushed (case-> [-E    -Γ -φ -τ -σ -Ξ -M → -ς]
                     [-e -ρ -Γ -φ -τ -σ -Ξ -M → -ς]))
;; Proceed to the next `eval` state with given frame `φ` pushed
(define -ς/pushed
  (case-lambda
    [(e ρ Γ φ τ σ Ξ M)
     (define FVs (FV e))
     (define ρ* (ρ↓ ρ FVs))
     (define Γ* (Γ↓ Γ FVs))
     (define E* (-↓ e ρ*))
     (define τ* (-τ E* Γ*))
     (define Ξ* (⊔ Ξ τ* (-κ φ τ)))
     (-ς E* Γ τ* σ Ξ* M)] ; important not to restrict `Γ` for precision
    [(E Γ φ τ σ Ξ M)
     (define τ* (-τ E Γ))
     (define Ξ* (⊔ Ξ τ* (-κ φ τ)))
     (-ς E Γ τ* σ Ξ* M)]))

(: rt-spurious? ([-φ.rt.@ -Γ] [-WVs] . ->* . Boolean))
;; Check whether a returned result is spurious
(define (rt-spurious? φ Γ [W (-W '() #f)])
  (match-define (-W Vs ?e) W)
  (match-define (-φ.rt.@ Γ₀ xs e_f e_xs) φ)
  (define params ; only care params that have corresponding args
    (for/set: : (Setof Symbol) ([x xs] [e_x e_xs] #:when e_x) x))

  ; Convert facts about parameters in new environment
  ; to facts about arguments in old environment
  ; PRECOND: (FV e) ⊆ xs
  (define (convert [e : -e]) : -e
    (for/fold ([e e]) ([x xs] [e_x e_xs] #:when e_x)
      (e/ e x e_x)))
  
  (define Γ*
    (for/set: : -Γ ([e Γ] #:when (⊆ (FV e) params))
      (convert e)))

  ; Check whether the propositions would contradict
  (define Γ₀* (Γ⊓ Γ₀ Γ*))
  (cond
    [Γ₀* (or (spurious? Γ₀* (-W Vs (and ?e (convert ?e))))
             (spurious? Γ₀* (-W Vs (apply -?@ e_f e_xs))))]
    [else #t]))


;;;;; For testing only

(define ↦* : (-ς* → -ς*)
  (match-lambda
    [(? set? s) (match/nd: #:tag ↦* (-ς → -ς) s [ς (↦ ς)])]
    [(? -ς? ς) (↦ ς)]))

(: dbg : Path-String → (Integer → -ς*))
(define ((dbg p) n)
  (for/fold ([ς* : -ς* (𝑰 (files->prog (list p)))])
            ([i (in-range n)])
    (↦* ς*)))
