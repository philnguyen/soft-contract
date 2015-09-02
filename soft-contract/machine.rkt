#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt")
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
    [ctx : Mon-Party])
  (struct -φ.set! [α : -α])
  (struct -φ.@ [es : (Listof -E)] [vs : (Listof -WV)] [ctx : Mon-Party])
  (struct -φ.begin [es : (Listof -e)] [env : -ρ])
  (struct -φ.begin0v [es : (Listof -e)] [env : -ρ])
  (struct -φ.begin0e [V : -WVs] [es : (Listof -e)] [env : -ρ])
  (struct -φ.mon.v [ctc : (U -E -WV)] [mon-info : Mon-Info])
  (struct -φ.mon.c [val : (U -E -WV)] [mon-info : Mon-Info])
  (struct -φ.indy.dom
    [pending : Symbol] ; variable for next current expression under evaluation
    [xs : (Listof Symbol)] ; remaining variables
    [cs : (Listof -?e)] ; remaining contracts
    [Cs : (Listof -V)] ; remaining contracts
    [args : (Listof -WV)] ; remaining arguments
    [args↓ : (Listof (Pairof Symbol -WV))] ; evaluated arguments
    [fun : -V] ; inner function
    [rng : -e] ; range
    [env : -ρ] ; range's context
    [mon-info : Mon-Info])
  (struct -φ.indy.rng [fun : -V] [args : (Listof -WV)] [mon-info : Mon-Info])
  (struct -φ.rt.@ [Γ : -Γ] [xs : (Listof Symbol)] [f : -?e] [args : (Listof -?e)])
  (struct -φ.rt.let [old-dom : (Setof Symbol)])
  ;; contract stuff
  (struct -φ.μc [x : Symbol])
  (struct -φ.struct/c
    [name : -id] [fields : (Listof -e)] [env : -ρ] [fields↓ : (Listof -WV)])
  (struct -φ.=>i
    [dom : (Listof -e)] [dom↓ : (Listof -V)] [cs↓ : (Listof -?e)] [xs : (Listof Symbol)]
    [rng : -e] [env : -ρ])
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
      [(? -v?) (values σ (close-Γ -Γ∅ (close e -ρ∅)))]
      [(-->i doms rng)
       (define-values (xs cs)
         (for/lists ([xs : (Listof Symbol)] [cs : (Listof -e)])
                    ([dom doms])
           (values (car dom) (cdr dom))))
       (define-values (σ* γs) (alloc-es σ cs))
       (values σ* (-=>i xs cs γs rng -ρ∅ -Γ∅))]
      [(-@ (-st-mk (-id (and t (or 'and/c 'or/c 'not/c)) 'Λ) _) cs _)
       (define-values (σ* αs) (alloc-es σ cs))
       (values σ* (-St (-id t 'Λ) αs))]
      [(-struct/c id cs)
       (define-values (σ* αs) (alloc-es σ cs))
       (values σ* (-St/C id αs))]
      [e (error '𝑰 "TODO: execute general expression. For now can't handle ~a"
                (show-e e))]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; PRETTY PRINTING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define show-τ : (-τ → Symbol) (unique-name 'τ))

(define show-φ : (-φ → Sexp)
  (match-lambda
    [(-φ.if t e) `(if ,(show-E t) ,(show-E e))]
    [(-φ.let-values x bnds bnds↓ _env body _ctx)
     `(let (,@(reverse
               (for/list : (Listof Sexp) ([(x W) (in-hash bnds↓)])
                 `[,x ,(show-WV W)]))
            [,x □]
            ,@(for/list : (Listof Sexp) ([bnd bnds])
                (match-define (cons x e_x) bnd)
                `[,x ,(show-e e_x)]))
        ,(show-e body))]
    [(-φ.letrec-values x bnds _env body _ctx)
     `(letrec ([,x □]
               ,@(for/list : (Listof Sexp) ([bnd bnds])
                   (match-define (cons x e_x) bnd)
                   `[,x ,(show-e e_x)]))
        ,(show-e body))]
    [(? -φ.set!?) `set!…]
    [(-φ.@ Es Ws _)
     `(,@(reverse (map show-V (map (inst -W-x -V) Ws)))
       □ ,@(map show-E Es))]
    [(-φ.begin es _) `(begin ,@(map show-e es))]
    [(-φ.begin0v es _) `(begin0 □ ,@(map show-e es))]
    [(-φ.begin0e (-W Vs _) es _)
     `(begin0 ,(map show-V Vs) ,@(map show-e es))]
    [(-φ.mon.v ctc _)
     `(mon ,(if (-E? ctc) (show-E ctc) (show-V (-W-x ctc))) □)]
    [(-φ.mon.c val _)
     `(mon □ ,(if (-E? val) (show-E val) (show-V (-W-x val))))]
    [(-φ.indy.dom x xs cs Cs args args↓ fun rng _env _l³)
     `(indy.dom
       [,@(reverse
           (for/list : (Listof Sexp) ([arg args↓])
             (match-define (cons x W_x) arg)
             `[,x ∈ ,(show-WV W_x)]))
        (,x □)
        ,@(for/list : (Listof Sexp) ([x xs] [c cs] [C Cs] [arg args])
            `(mon ,(show-WV (-W C c)) ,(show-WV arg) as ,x))
        ↦ ,(show-e rng)]
       ,(show-V fun))]
    [(-φ.indy.rng fun args _)
     `(indy.rng (mon □ (,(show-V fun) ,@(map show-WV args))))]
    [(-φ.rt.@ Γ xs f args)
     `(rt ,(show-Γ Γ) (,(show-?e f)
                       ,@(for/list : (Listof Sexp) ([x xs] [arg args])
                           `(,x ↦ ,(show-?e arg)))))]
    [(-φ.rt.let dom) `(rt/let ,@(set->list dom))]
    [(-φ.μc x) `(μ/c ,x □)]
    [(-φ.struct/c id cs _ρ cs↓)
     `(,(-id-name (id/c id))
       ,@(reverse (map show-WV cs↓))
       □
       ,@(map show-e cs))]
    [(-φ.=>i cs Cs↓ cs↓ xs e ρ)
     `(=>i ,@(reverse (map show-V Cs↓)) □ ,@(map show-e cs))]
    ))

(define (show-κ [κ : -κ]) : Sexp
  (match-define (-κ φ τ) κ)
  `(,(show-φ φ) ↝ ,(show-τ τ)))

(define (show-Ξ [Ξ : -Ξ]) : (Listof Sexp)
  (for/list : (Listof Sexp) ([(τ κs) Ξ])
    `(,(show-τ τ) ↦ ,@(for/list : (Listof Sexp) ([κ κs]) (show-κ κ)))))

(define (show-ς [ς : -ς]) : (Listof Sexp)
  (match-define (-ς E Γ τ σ Ξ M) ς)
  `((E: ,(show-E E))
    (Γ: ,@(show-Γ Γ))
    (τ: ,(show-τ τ))
    (σ: ,@(show-σ σ))
    (Ξ: ,@(show-Ξ Ξ))))
