#lang typed/racket/base

(require
 racket/match
 "../utils.rkt" "../ast.rkt" "../runtime.rkt" "../provability.rkt" "../machine.rkt"
 "step-app.rkt" "step-mon.rkt")

(provide ↦e)

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
          (-Δς (-blm 'TODO 'Λ (-st-p (-struct-info (-id-local 'defined 'Λ) 1 ∅))
                     (list 'undefined))
              Γ κ '() '() '())]
         [_ (-Δς W Γ κ '() '() '())]))]
    ;; look up top-level reference
    [(and ref (-ref (and id (-id-local name ctx*)) ctx pos))
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
               [C (↦mon (-W C #f #|TODO|#) (-W V ref) Γ κ σ Ξ M (list ctx* ctx ctx*) pos)])])])]
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
         [(null? x) (values (-St -s-null '()) -null)]
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
     (↦e e* ρ Γ (-kont (-φ.set! x (ρ@ ρ x)) κ) σ Ξ M)]
    ;; @-havoc
    [(-@-havoc x)
     (define (mk-args [n : Integer]) : (Listof -WV) ; FIXME hack
       (build-list n (λ ([i : Integer])
                       (define e (string->symbol (format "z•~a" (n-sub i))))
                       (-W -●/V (-x e)))))
     (match/nd: (-V → -Δς) (σ@ σ (ρ@ ρ x))
       [(and V (or (-Clo* xs _ _) (-Clo xs _ _ _)))
        (define n
          (match xs
            [(? list?) (length xs)]
            [(-varargs zs _) (+ 1 (length zs))]))
        (↦@ (-W V x) (mk-args n) Γ κ σ Ξ M -havoc-src)]
       [(and V (-Ar xs _ _ _ _ _ _ _))
        (↦@ (-W V x) (mk-args (length xs)) Γ κ σ Ξ M -havoc-src)]
       [V
        (log-debug "havoc: ignore first-order value ~a" (show-V V))
        ∅])]
    ;; amb
    [(-amb es)
     (match/nd: (-e → -Δς) es
       [ei (↦e ei ρ Γ κ σ Ξ M)])]
    ;; contract stuff
    [(-μ/c x c _)
     (error '↦e "TODO: μ/c")]
    [(-->i doms rng pos)
     (match doms
       ['()
        (define C (-=>i '() '() '() rng ρ Γ))
        (-Δς (-W (list C) e) Γ κ '() '() '())]
       [(cons dom doms*)
        (match-define (cons x c) dom)
        (define-values (xs* cs*) (unzip doms*))
        (↦e c ρ Γ (-kont (-φ.=>i cs* '() '() (cons x xs*) rng ρ pos) κ) σ Ξ M)])]
    [(-x/c x)
     (error '↦e "TODO: x/c")]
    [(-struct/c id cs pos)
     (match cs
       ['() (-Δς (-W (list (-St/C '✓ id '())) e) Γ κ '() '() '())]
       [(cons c cs*)
        (↦e c ρ Γ (-kont (-φ.struct/c id cs* ρ '() pos) κ) σ Ξ M)])]
    ))
