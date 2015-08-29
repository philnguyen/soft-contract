#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(provide (all-defined-out)) ; TODO

;; Continuation frames
(define-data -φ
  (struct -φ.if [t : -E] [e : -E])
  (struct -φ.let-values
    [pending : (Listof Symbol)]
    [bnds : (Listof (Pairof (Listof Symbol) -e))]
    [bnds↓ : (Map Symbol -WV)]
    [env : -ρ]
    [body : -e]
    [ctx : Mon-Party])
  (struct -φ.letrec-values
    [pending : (Listof Symbol)]
    [bnds : (Listof (Pairof (Listof Symbol) -e))]
    [env : -ρ]
    [body : -e]
    [ctx : Mon-Party]
    [old-dom : (Setof Symbol)])
  (struct -φ.set! [α : -α])
  (struct -φ.@ [es : (Listof -E)] [vs : (Listof -WV)] [ctx : Mon-Party])
  (struct -φ.begin [es : (Listof -e)] [env : -ρ])
  (struct -φ.begin0v [es : (Listof -e)] [env : -ρ])
  (struct -φ.begin0e [V : -WVs] [es : (Listof -e)] [env : -ρ])
  (struct -φ.mon.v [ctc : (U -E -WV)] [mon-info : Mon-Info])
  (struct -φ.mon.c [val : (U -E -WV)] [mon-info : Mon-Info])
  (struct -φ.indy.dom
    [pending : Symbol]
    [doms : (Listof (Pairof Symbol -WV))]
    [args : (Listof -WV)]
    [args↓ : (Listof (Pairof Symbol -WV))]
    [fun : -V]
    [rng : -↓]
    [mon-info : Mon-Info])
  (struct -φ.indy.rng [fun : -V] [args : (Listof -WV)] [min-info : Mon-Info])
  (struct -φ.rt.@ [Γ : -Γ] [xs : (Listof Symbol)] [f : -?e] [args : (Listof -?e)])
  (struct -φ.rt.let [old-dom : (Setof Symbol)])
  ;; contract stuff
  (struct -φ.μc [x : Symbol])
  (struct -φ.struct/c
    [name : -id] [fields : (Listof -e)] [env : -ρ] [fields↓ : (Listof -WV)])
  ;(struct -φ.=> [dom : (Listof -e)] [dom↓ : (Listof -WV)] [env : -ρ])
  (struct -φ.=>i
    [dom : (Listof -e)] [dom↓ : (Listof -WV)] [xs : (Listof Symbol)] [rng : -e] [env : -ρ])
  )

;; Stack address
(struct -τ ([E : (U -E #|HACK|# (Listof (U Symbol -E)))] [Γ : -Γ]) #:transparent)
;; Stack
(struct -κ ([top : -φ] [nxt : -τ]) #:transparent)

(define-type -Ξ (MMap -τ -κ))

;; (narrow) state
(struct -ς ([e : -E] [Γ : -Γ] [τ : -τ] [σ : -σ] [Ξ : -Ξ] [M : -M]) #:transparent)

(define-type -ς* (U -ς (Setof -ς)))

(: 𝑰 : -prog → -ς)
;; Load program to intial machine state
;; FIXME: allow expressions in top-levels and execute them instead,
;;        then initialize top-levels to `undefined`
(define (𝑰 p)
  (match-define (-prog ms e₀) p)

  (: alloc-es : -σ (Listof -e) → (Values -σ (Listof -α)))
  (define (alloc-es σ es)
    (define-values (σ* αs-rev)
      (for/fold ([σ* : -σ σ] [αs-rev : (Listof -α) '()])
                ([e es])
        (define-values (σ** V) (alloc-e σ* e))
        (define α (-α.val e))
        (values (⊔ σ** α V) (cons α αs-rev))))
    (values σ* (reverse αs-rev)))

  (: alloc-e : -σ -e → (Values -σ -V))
  (define (alloc-e σ e)
    (match e
      [(? -v?) (values σ (close e -ρ∅ -Γ∅))]
      [(-->i doms rng)
       (define-values (xs cs)
         (for/lists ([xs : (Listof Symbol)] [cs : (Listof -e)])
                    ([dom doms])
           (values (car dom) (cdr dom))))
       (define-values (σ* γs) (alloc-es σ cs))
       (values σ* (-=>i (map (inst cons Symbol -α) xs γs) rng -ρ∅ -Γ∅))]
      [(-@ (-st-mk (-id (and t (or 'and/c 'or/c 'not/c)) 'Λ) _) cs _)
       (define-values (σ* αs) (alloc-es σ cs))
       (values σ* (-St (-id t 'Λ) αs))]
      [(-struct/c id cs)
       (define-values (σ* αs) (alloc-es σ cs))
       (values σ* (-St/C id αs))]
      [e (error '𝑰 "TODO: execute general expression. For now can't handle ~a"
                (show-e σ e))]))

  ;; Assuming each top-level variable binds a value for now.
  ;; TODO generalize.
  (define σ₀
    (for*/fold ([σ : -σ -σ∅])
               ([m ms]
                [form (-plain-module-begin-body (-module-body m))])
      (define mod-path (-module-path m))
      (match form
        ;; general top-level form
        [(? -e?) σ]
        [(-define-values ids e)
         (cond
           [(= 1 (length ids))
            (define-values (σ* V) (alloc-e σ e))
            (⊔ σ* (-α.def (-id (car ids) mod-path)) V)]
           [else
            (error '𝑰 "TODO: general top-level. For now can't handle `define-~a-values`"
                   (length ids))])]
        [(? -require?) σ]
        ;; provide
        [(-provide specs)
         (for/fold ([σ : -σ σ]) ([spec specs])
           (match-define (-p/c-item x c) spec)
           (define-values (σ₁ C) (alloc-e σ c))
           (define id (-id x mod-path))
           (define σ₂ (⊔ σ₁ (-α.ctc id) C))
           (cond
             [(hash-has-key? σ₂ (-α.def id)) σ₂]
             [else (⊔ σ₂ (-α.def id) '•)]))]
        ;; submodule-form
        [(? -module?) (error '𝑰 "TODO: sub-module forms")])))

  (define E₀ (-↓ e₀ -ρ∅))
  (define τ₀ (-τ E₀ -Γ∅))

  (-ς E₀ -Γ∅ τ₀ σ₀ (hash τ₀ ∅) (hash)))

(: final? (case-> [-ς → Boolean]
                  [-E -τ -Ξ → Boolean]))
(define final?
  (case-lambda
    [(E τ Ξ) (and (set-empty? (hash-ref Ξ τ)) (-Ans? E))]
    [(ς)
     (match-define (-ς E _ τ _ Ξ M) ς)
     (final? E τ Ξ)]))

(define (show-ς [ς : -ς]) : Sexp
  (match-define (-ς E Γ τ σ Ξ M) ς)

  (define (show-τ [τ : -τ]) : Sexp
    (match-define (-τ E Γ) τ)
    (cond
      [(-E? E) `(τ: ,(show-E σ E) ,(show-Γ Γ))]
      [else `(τ: … ,(show-Γ Γ))]))

  (define show-φ : (-φ → Sexp)
    (match-lambda
      [(-φ.if t e) `(if ,(show-E σ t) ,(show-E σ e))]
      [(? -φ.let-values?) `let-values…]
      [(? -φ.letrec-values?) `letrec-values…]
      [(? -φ.set!?) `set!…]
      [(-φ.@ Es Ws _)
       `(,@(map (curry show-E σ) Es) ○
         ,@(reverse (map (curry show-V σ) (map (inst -W-x -V) Ws))))]
      [(-φ.begin es _) (map (curry show-e σ) es)]
      [_ 'φ•]))

  (define (show-κ [κ : -κ]) : Sexp
    (match-define (-κ φ τ) κ)
    `(κ: ,(show-φ φ) ,(show-τ τ)))

  (define show-Ξ
    (for/list : (Listof Sexp) ([(τ κs) (in-hash Ξ)])
      `(,(show-τ τ) ↦ ,@(for/list : (Listof Sexp) ([κ κs]) (show-κ κ)))))
  
  `(,(show-E σ E)
    ,(show-Γ Γ)
    ,(show-τ τ)
    ,(show-σ σ)
    ,show-Ξ))

(define (show-ς* [ς* : -ς*]) : Sexp
  (cond
    [(-ς? ς*) (show-ς ς*)]
    [else (for/list : (Listof Sexp) ([ς ς*])
            (show-ς ς))]))
