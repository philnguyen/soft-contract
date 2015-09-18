#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "provability.rkt" "delta.rkt" "machine.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(provide ↦)

(: with-Δ : -Δσ -ΔΞ -ΔM -Δς* → -Δς*)
;; Append store deltas to given state delta
(define (with-Δ δσ δΞ δM δς)
  (match/nd: (-Δς → -Δς) δς
    [(-Δς E Γ κ δσ* δΞ* δM*)
     (-Δς E Γ κ (append δσ δσ*) (append δΞ δΞ*) (append δM δM*))]))

(: ↦ : -ς → -Δς*)
;; Steps a full state in the CEΓKSΞ machine
(define ↦
  (match-lambda
    [(-ς (-↓ e ρ) Γ κ σ Ξ M)
     (↦e e ρ Γ κ σ Ξ M)]
    [(-ς (-Mon C V l³) Γ κ σ Ξ M)
     (↦mon C V Γ κ σ Ξ M l³)]
    [(-ς (-FC C V l) Γ κ σ Ξ M)
     (↦FC C V Γ κ σ Ξ M l)]
    [(-ς (? -W? W) Γ κ σ Ξ M)
     (↦κ W Γ κ σ Ξ M)]
    [(-ς (? -blm? blm) Γ κ σ Ξ M)
     (match κ
       [(? -τ? τ)
        (match/nd: (-kont → -Δς) (hash-ref Ξ τ)
          [κ* (↦blm blm Γ κ* σ Ξ M)])]
       [_ (↦blm blm Γ κ σ Ξ M)])]
    [ς (error '↦ "unexpected: ~a" ς)]))

(: ↦e : -e -ρ -Γ -κ -σ -Ξ -M → -Δς*)
;; Stepping rules for "eval" states
(define (↦e e ρ Γ κ σ Ξ M)
  (match e
    ;; close value
    [(? -v? v)
     (-Δς (-W (list (close v ρ)) v) Γ κ '() '() '())]
    ;; look up variable
    [(? -x? x)
     (for*/set: : (Setof -Δς) ([V (σ@ σ (ρ@ ρ x))]
                               [W (in-value (-W (list V) (canonicalize Γ x)))]
                               #:unless (spurious? M σ Γ W))
       (match V
         ['undefined ; FIXME hack
          (-Δς (-blm 'TODO 'Λ (-st-p (-id 'defined 'Λ) 1) (list 'undefined))
              Γ κ '() '() '())]
         [_ (-Δς W Γ κ '() '() '())]))]
    ;; look up top-level reference
    [(and ref (-ref (and id (-id name ctx*)) ctx))
     (cond
       ;; skip contract checking for self reference
       [(equal? ctx ctx*)
        (for/set: : (Setof -Δς) ([V (σ@ σ (-α.def id))])
          (-Δς (-W (list V) ref) Γ κ '() '() '()))]
       ;; perform contract checking for cross-module reference
       [else
        ;; FIXME
        (define Vs (σ@ σ (-α.def id)))
        (define Cs (σ@ σ (-α.ctc id)))
        (match/nd: (-V → -Δς) Vs
          [V (match/nd: (-V → -Δς) Cs
               [C (↦mon (-W C #f #|TODO|#) (-W V ref) Γ κ σ Ξ M (list ctx* ctx ctx*))])])])]
    ;; evaluate function position, pushing arguments
    [(-@ f xs l)
     (define κ* (-kont (-φ.@ (for/list : (Listof -E) ([x xs]) (-⇓ x ρ)) '() l) κ))
     (↦e f ρ Γ κ* σ Ξ M)]
    ;; evaluate scrutiny, pushing branches
    [(-if e₀ e₁ e₂)
     (↦e e₀ ρ Γ (-kont (-φ.if (-⇓ e₁ ρ) (-⇓ e₂ ρ)) κ) σ Ξ M)]
    ;; ignore continuation marks for now
    [(-wcm e_k e_v e_b)
     (error '↦e "TODO: wcm")]
    ;; evaluate first clause in `begin` and push remaining clauses
    [(-begin es)
     (match es
       [(list) (-Δς (-W -Void/Vs (-?@ -void)) Γ κ '() '() '())]
       [(list e*) (↦e e* ρ Γ κ σ Ξ M)]
       [(cons e* es*)
        (↦e e* ρ Γ (-kont (-φ.begin es* ρ) κ) σ Ξ M)])]
    ;; evaluate first clause in `begin0` and push the remaining clauses
    [(-begin0 e₀ es)
     (cond
       [(null? es) (↦e e₀ ρ Γ κ σ Ξ M)]
       [else
        (↦e e₀ ρ Γ (-kont (-φ.begin0v es ρ) κ) σ Ξ M)])]
    ;; quote
    [(-quote x)
     (define-values (V ?e)
       (cond
         [(Base? x) (values (-b x) (-b x))]
         [(null? x) (values (-St (-id 'null 'Λ) '()) -null)]
         [else (error '↦e "TODO: quote")]))
     (-Δς (-W (list V) ?e) Γ κ '() '() '())]
    ;; let-values: evaluate the first argument (if there is) and push the rest
    [(-let-values bnds e* l)
     (match bnds
       ['() (↦e e* ρ Γ κ σ Ξ M)]
       [(cons (cons xs eₓ) bnds*)
        (↦e eₓ ρ Γ (-kont* (-φ.let-values xs bnds* (hash) ρ e* l) κ) σ Ξ M)])]
    ;; letrec-values
    [(-letrec-values bnds e l)
     (match bnds
       ['() (↦e e ρ Γ κ σ Ξ M)]
       [(cons (cons xs e*) bnds*)
        ;; Extend environment with each variable initialized to `undefined`
        (define-values (ρ* σ* δσ)
          (for*/fold ([ρ* : -ρ ρ] [σ* : -σ σ] [δσ : -Δσ '()])
                     ([bnd bnds] [xs (in-value (car bnd))])
            (for/fold ([ρ* : -ρ ρ*] [σ* : -σ σ*] [δσ : -Δσ δσ])
                      ([x xs] [e_x (split-values e* (length xs))])
              (define α x #;(-α.bnd x e_x Γ))
              (values (ρ+ ρ* x α)
                      (⊔ σ α 'undefined)
                      (cons (cons α 'undefined) δσ)))))
        (define κ* (-kont* (-φ.letrec-values xs bnds* ρ* e l)
                           (-φ.rt.let (dom ρ))
                           κ))
        (with-Δ δσ '() '() (↦e e* ρ* Γ κ* σ* Ξ M))])]
    [(-set! x e*)
     (↦e e* ρ Γ (-kont (-φ.set! (ρ@ ρ x)) κ) σ Ξ M)]
    ;; @-havoc
    [(-@-havoc x)
     (define (mk-args [n : Integer]) : (Listof -WV) ; FIXME hack
       (build-list n (λ ([i : Integer])
                       (define e (string->symbol (format "z•~a" (n-sub i))))
                       (-W '• (-x e)))))
     (match/nd: (-V → -Δς) (σ@ σ (ρ@ ρ x))
       [(and V (or (-Clo* xs _ _) (-Clo xs _ _ _)))
        (define n
          (match xs
            [(? list?) (length xs)]
            [(-varargs zs _) (+ 1 (length zs))]))
        (↦@ (-W V x) (mk-args n) Γ κ σ Ξ M ☠)]
       [(and V (-Ar xs _ _ _ _ _ _ _))
        (↦@ (-W V x) (mk-args (length xs)) Γ κ σ Ξ M ☠)]
       [V
        (log-debug "havoc: ignore first-order value ~a" (show-V V))
        ∅])]
    ;; amb
    [(-amb es)
     (match/nd: (-e → -Δς) es
       [ei (↦e ei ρ Γ κ σ Ξ M)])]
    ;; contract stuff
    [(-μ/c x c)
     (error '↦e "TODO: μ/c")]
    [(-->i doms rng)
     (match doms
       ['()
        (define C (-=>i '() '() '() rng ρ Γ))
        (-Δς (-W (list C) e) Γ κ '() '() '())]
       [(cons dom doms*)
        (match-define (cons x c) dom)
        (define-values (xs* cs*) (unzip doms*))
        (↦e c ρ Γ (-kont (-φ.=>i cs* '() '() (cons x xs*) rng ρ) κ) σ Ξ M)])]
    [(-x/c x)
     (error '↦e "TODO: x/c")]
    [(-struct/c id cs)
     (match cs
       ['() (-Δς (-W (list (-St/C id '())) e) Γ κ '() '() '())]
       [(cons c cs*)
        (↦e c ρ Γ (-kont (-φ.struct/c id cs* ρ '()) κ) σ Ξ M)])]
    ))

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
                   (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) 'Λ) -ρ⊥ -Γ⊤)
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
    [(-φ.set! α)
     (with-guarded-arity 1 'TODO 'set!
       (define Γ* #|FIXME update!!|# Γ)
       ; TODO: might not need to erase (set! x _)
       (-Δς (-W -Void/Vs #f) Γ* κ (list (cons α (first Vs))) '() '()))]
    ;; Application
    [(-φ.@ Es WVs↓ l)
     (with-guarded-arity 1 l 'apply
       (match-define (list V) Vs)
       (define WVs↓* (cons (-W V ?e) WVs↓))
        (match Es
          ['()
           (match-define (cons W_f W_xs) (reverse WVs↓*))
           (↦@ W_f W_xs Γ κ σ Ξ M l)]
          ;; Swap next argument for evaluation
          [(cons E* Es*)
           (-Δς E* Γ (-kont (-φ.@ Es* WVs↓* l) κ) '() '() '())]))]
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
    [(-φ.mon.c E (and l³ (list _ _ lo)))
     (with-guarded-arity 1 lo 'Λ
       (match-define (list C) Vs)
       (define W_C (-W C ?e))
       (cond
         [(-WV? E) (↦mon W_C E Γ κ σ Ξ M l³)]
         [else (-Δς E Γ (-kont (-φ.mon.v W_C l³) κ) '() '() '())]))]
    ; waiting on the value to be checked
    [(-φ.mon.v C (and l³ (list l+ _ lo)))
     (with-guarded-arity 1 l+ lo
       (match-define (list V) Vs)
       (define W_V (-W V ?e))
       (cond
         [(-WV? C) (↦mon C W_V Γ κ σ Ξ M l³)]
         [else (-Δς C Γ (-kont (-φ.mon.c W_V l³) κ) '() '() '())]))]
    ;; indy
    [(-φ.indy.dom x xs cs Cs W_xs doms↓ V_f d ρ_d l³)
     (with-guarded-arity 1 'Λ 'Λ
       (match-define (list V) Vs)
       (define l³* (swap-parties l³))
       (define doms↓* (cons (cons x (-W V ?e)) doms↓))
       (match* (xs cs Cs W_xs)
         [('() '() '() '())
          (define args (map (inst cdr Symbol -WV) (reverse doms↓*))) ; TODO
          (↦e d ρ_d Γ (-kont (-φ.indy.rng V_f args l³) κ) σ Ξ M)]
         [((cons x* xs*) (cons c* cs*) (cons C* Cs*) (cons W_x* W_xs*))
          (define W_c* (-W C* c*))
          (define κ* (-kont (-φ.indy.dom x* xs* cs* Cs* W_xs* doms↓* V_f d ρ_d l³) κ))
          (↦mon W_c* W_x* Γ κ* σ Ξ M l³*)]))]
    [(-φ.indy.rng V_f args l³)
     (match-define (list l+ l- lo) l³)
     (with-guarded-arity 1 lo 'Λ
       (match-define (list V) Vs)
       (define W_d (-W V ?e))
       (define W_f (-W V_f (-x 'f•))) ; FIXME temp. hack
       (define κ* (-kont (-φ.mon.v W_d l³) κ))
       (↦@ W_f args Γ κ* σ Ξ M lo))]
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
    [(-φ.μc x)
     (match Vs
       [(list V) (error '↦WVs "TODO: μ/c")]
       [_ (error '↦WVs "TODO: catch arity error for μ/c")])]
    [(-φ.struct/c id es ρ WVs↓)
     (with-guarded-arity 1 'TODO 'Λ
       (match-define (list V) Vs)
       (define WVs↓* (cons (-W V ?e) WVs↓))
       (match es
         ['()
          (define n (length WVs↓*))
          (define-values (αs σ* es* δσ)
            ; accumulate new store and address list
            ; which is reversed compard to `WVs↓*`, hence of the right order
            (for/fold ([αs : (Listof -α) '()] [σ* : -σ σ] [es* : (Listof -?e) '()] [δσ : -Δσ '()])
                      ([WV WVs↓*] [i (in-range n)])
              (match-define (-W V e) WV)
              (define α
                (cond [e (-α.val e)]
                      [else (-α.opq (id/c id) #f #|FIXME|# i)]))
              (values (cons α αs)
                      (⊔ σ* α V)
                      (cons e es*)
                      (cons (cons α V) δσ))))
          (define C (-St/C id αs))
          (define e_C (-?struct/c id es*))
          (-Δς (-W (list C) e_C) Γ κ δσ '() '())]
         [(cons e es*)
          (↦e e ρ Γ (-kont (-φ.struct/c id es* ρ WVs↓*) κ) σ Ξ M)]))]
    [(-φ.=>i cs Cs↓ cs↓ xs rng ρ)
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
              (define γ
                (cond [c (-α.val c)]
                      [else (-α.opq (-id '->/i 'Λ) #f #|TODO|# i)]))
              (values (cons γ γs)
                      (⊔ σ* γ C)
                      (cons c cs*)
                      (cons (cons γ C) δσ))))
          (define C (-=>i xs cs* γs rng ρ Γ))
          (define e_C (-?->i xs cs* rng))
          (-Δς (-W (list C) e_C) Γ κ δσ '() '())]
         [(cons c cs*)
          (↦e c ρ Γ (-kont (-φ.=>i cs* Cs↓* cs↓* xs rng ρ) κ) σ Ξ M)]))]
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

(: ↦@ : -WV (Listof -WV) -Γ -κ -σ -Ξ -M Mon-Party → -Δς*)
;; Stepping rules for function application
(define (↦@ W_f W_xs Γ κ σ Ξ M l)

  (match-define (-W V_f e_f) W_f)
  (define-values (V_xs e_xs) ((inst unzip-by -WV -V -?e) -W-x -W-e W_xs))
  (define e_a (apply -?@ e_f e_xs))

  (dbg '↦@ "App:~n f: ~a~n xs: ~a~n" (show-V V_f) (map show-V V_xs))

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
       (define Ξ* (⊔ Ξ τ κ*))
       (with-Δ δσ δΞ '() (↦e e ρ* Γ_f τ σ* Ξ* M))]
      [(-varargs zs z) (error '↦@ "TODO: varargs")]))

  (: ↦δ : -o → -Δς*)
  (define (↦δ o)
    (define-values (δσ AΓs) (δ M σ Γ o W_xs l))
    (match/nd: (-AΓ → -Δς) AΓs
      [(-AΓ (? -blm? blm) Γ*) (-Δς blm         Γ* κ δσ '() '())]
      [(-AΓ (? list? Vs ) Γ*) (-Δς (-W Vs e_a) Γ* κ δσ '() '())]))
  
  (: ↦havoc : → (Setof -Δς))
  (define (↦havoc)
    (define V_havoc (σ@₁ σ (-α.def havoc-id)))
    (define W_havoc (-W V_havoc (-ref havoc-id l)))
    (for/fold ([acc : (Setof -Δς) ∅]) ([W_x W_xs])
      (match (↦@ W_havoc (list W_x) Γ κ σ Ξ M 'Λ)
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
       (define κ₂ (-kont (-φ.indy.rng V_g '() l³) κ₁))
       (↦e d ρ_d Γ_d κ₂ σ Ξ M)]
      [((cons x xs*) (cons c cs*) (cons C Cs*) (cons W_x W_xs*))
       (define l³* (swap-parties l³))
       (define W_c (-W C c))
       (define W_x* (-W (-W-x W_x) (-x x)))
       (define κ₂ (-kont (-φ.indy.dom x xs* cs* Cs* W_xs* '() V_g d ρ_d l³) κ₁))
       (↦mon W_c W_x* Γ_d κ₂ σ Ξ M l³*)]))
  
  (match V_f
    [(? -o? o) (↦δ o)]
    [(-Clo* xs e ρ_f    ) (↦β xs e ρ_f (Γ↓ Γ (dom ρ_f)))]
    [(-Clo  xs e ρ_f Γ_f) (↦β xs e ρ_f Γ_f)]
    [(-Ar xs cs γs d ρ_c Γ_c α l³)
     (match/nd: ((Listof -V) → -Δς) (σ@/list σ γs) ; TODO can explode very fast!!
       [Cs (match/nd: (-V → -Δς) (σ@ σ α)
             [V_g (↦indy xs cs Cs d ρ_c Γ_c V_g l³)])])]
    ['• (set-add (↦havoc) (↦opq))]
    [_ (-Δς (-blm l 'apply 'procedure? (list V_f)) Γ κ '() '() '())]))

(: ↦mon : -WV -WV -Γ -κ -σ -Ξ -M Mon-Info → -Δς*)
;; Stepping rules for contract monitoring
(define (↦mon W_c W_v Γ κ σ Ξ M l³)
  (match-define (-W C e_c) W_c)
  (match-define (-W V e_v) W_v)
  (match-define (list l+ l- lo) l³)

  (match (MσΓ⊢V∈C M σ Γ W_v W_c)
    ['✓
     (define Γ* (Γ+ Γ (-?@ e_c e_v)))
     (-Δς (-W (list V) e_v) Γ* κ '() '() '())]
    ['X
     (define Γ* (Γ+ Γ (-not (-?@ e_c e_v))))
     (-Δς (-blm l+ lo C (list V)) Γ* κ '() '() '())]
    ['?
     (match C
       [(-=>i xs cs Cs d ρ_d Γ_d)
        ;; TODO: check for arity also
        (define-values (Γ-ok Γ-bad) (Γ+/-W∈W M σ Γ W_v (-W 'procedure? 'procedure?)))
        (define ς-ok
          (and Γ-ok
               (let ()
                 (define α
                   (cond [e_v (-α.val e_v)]
                         [else (-α.opq (-id 'Ar 'Λ) #f #|FIXME|# 1)]))
                 (define Ar (-Ar xs cs Cs d ρ_d Γ_d α l³))
                 (define δσ (list (cons α V)))
                 (-Δς (-W (list Ar) e_v #|TODO|#) Γ-ok κ δσ '() '()))))
        (define ς-bad
          (and Γ-bad
               (-Δς (-blm l+ lo 'procedure? (list V)) Γ-bad κ '() '() '())))
        (cond
          [(and ς-ok ς-bad) {set ς-ok ς-bad}]
          [ς-ok ς-ok]
          [ς-bad ς-bad]
          [else (error '↦mon "impossible")])]
       [(-St/C id γs)
        (define n (length γs))
        (define k? (-st-p id n))
        (define k (-st-mk id n))
        (define-values (Γ-ok Γ-bad) (Γ+/-W∈W M σ Γ W_v (-W k? k?)))
        (define ς-bad
          (and Γ-bad
               (-Δς (-blm l+ lo k? (list V)) Γ-bad κ '() '() '())))
        (define ς-ok
          (and Γ-ok
               (let ()
                 (define Vss : (Setof (Listof -V))
                   (match V
                     [(-St _ αs) (σ@/list σ αs)]
                     [_ {set (make-list n '•)}]))
                 (define Dss : (Setof (Listof -V)) (σ@/list σ γs))
                 (define e_ds (-struct/c-split e_c n))
                 (define e_vs (-struct-split   e_v id n))
                 (for*/set: : (Setof -Δς) ([Ds Dss] [Vs Vss])
                   (define mons : (Listof -Mon)
                     (for/list ([D Ds] [V Vs] [e_d e_ds] [e_vi e_vs])
                       (-Mon (-W D e_d) (-W V e_vi) l³)))
                   (match mons
                     ['() (-Δς (-W (list (-St id '())) (-?@ k)) Γ-ok κ '() '() '())]
                     [(cons mon mons*)
                      (define κ* (-kont (-φ.@ mons* (list (-W k k)) lo) κ))
                      (-Δς mon Γ-ok κ* '() '() '())])))))
        (cond
          [(and ς-ok ς-bad) (set-add ς-ok ς-bad)]
          [ς-ok ς-ok]
          [ς-bad ς-bad]
          [else (error '↦mon "impossible")])]
       [(-μ/C x c)
        (error '↦mon "μ/c")]
       [(-X/C x)
        (error '↦mon "ref")]
       [(-St (-id 'and/c 'Λ) (list γ₁ γ₂))
        (define Cs₁ (σ@ σ γ₁))
        (define Cs₂ (σ@ σ γ₂))
        (define-values (c₁ c₂) (-and/c-split e_c))
        (match/nd: (-V → -Δς) Cs₁
          [C₁
           (match/nd: (-V → -Δς) Cs₂
             [C₂
              (define κ* (-kont (-φ.mon.v (-W C₂ c₂) l³) κ))
              (define W_c₁ (-W C₁ c₁))
              (↦mon W_c₁ W_v Γ κ* σ Ξ M l³)])])]
       [(-St (-id 'or/c 'Λ) (list γ₁ γ₂))
        (define Cs₁ (σ@ σ γ₁))
        (define Cs₂ (σ@ σ γ₂))
        (define-values (c₁ c₂) (-or/c-split e_c))
        (match/nd: (-V → -Δς) Cs₁
          [C₁
           (cond
             [(C-flat? σ C₁)
              (match/nd: (-V → -Δς) Cs₂
                [C₂
                 (define κ* (-kont (-φ.if (-Mon (-W C₂ c₂) W_v l³)
                                          (-blm l+ lo C₁ (list V)))
                                   κ))
                 (define E* (-FC (-W C₁ c₁) W_v lo))
                 (-Δς E* Γ κ* '() '() '())])]
             [else
              (-Δς (-blm lo 'Λ #|hack|# (-st-p (-id 'flat-contract? 'Λ) 1) (list C₁))
                   Γ κ '() '() '())])])]
       [(-St (-id 'not/c 'Λ) (list α))
        (match/nd: (-V → -Δς) (σ@ σ α)
          [C*
           (cond
             [(C-flat? σ C*)
              (define κ* (-kont (-φ.if (-blm l+ lo C (list V)) (-W (list V) e_v)) κ))
              (-Δς (-FC (-W C* (-not/c-neg e_c)) W_v lo) Γ κ* '() '() '())]
             [else
              (-Δς (-blm lo 'Λ #|hack|# (-st-p (-id 'flat-contract? 'Λ) 1) (list C*))
                   Γ κ '() '() '())])])]
       [_
        (define κ* (-kont (-φ.if (-W (list V) e_v) (-blm l+ lo C (list V))) κ))
        (↦@ W_c (list W_v) Γ κ* σ Ξ M lo)])]))

(: ↦FC : -WV -WV -Γ -κ -σ -Ξ -M Mon-Party → -Δς*)
;; Stepping rules for monitoring flat contracts
(define (↦FC W_c W_v Γ κ σ Ξ M l)
  (match-define (-W C e_c) W_c)
  (match-define (-W V e_v) W_v)
  (match C
    [(-St (-id (and t (or 'and/c 'or/c)) 'Λ) (list γ₁ γ₂))
     (define Cs₁ (σ@ σ γ₁))
     (define Cs₂ (σ@ σ γ₂))
     (define-values (c₁ c₂) (-and/c-split e_c))
     (match/nd: (-V → -Δς) Cs₁
       [C₁
        (match/nd: (-V → -Δς) Cs₂
          [C₂
           (define φ
             (match t
               ['and/c (-φ.if (-FC W_v (-W C₂ c₂) l) (-W (list -ff) -ff))]
               ['or/c  (-φ.if (-W (list -tt) -tt) (-FC W_v (-W C₂ c₂) l))]))
           (-Δς (-FC (-W C₁ c₁) W_v l) Γ (-kont φ κ) '() '() '())])])]
    [(-St (-id 'not/c 'Λ) (list γ))
     (match/nd: (-V → -Δς) (σ@ σ γ)
       [C*
        (define κ* (-kont (-φ.@ '() (list (-W 'not 'not)) 'Λ) κ))
        (-Δς (-FC (-W C* (-not/c-neg e_c)) W_v l) Γ κ* '() '() '())])]
    ;; FIXME recursive contract
    [_ (↦@ W_c (list W_v) Γ κ σ Ξ M l)]))

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
  ; TODO: pass `M` and `σ`
  (define Γ₀* (Γ⊓ Γ₀ facts*))
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
