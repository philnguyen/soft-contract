#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "ast.rkt" "runtime.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(provide (all-defined-out))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Closure forms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-data -E
  (struct -↓ [e : -e] [ρ : -ρ])
  ; `V` and `e` don't have any reference back to `E`, so it's not recursive
  (struct -Mon [c : -WV] [v : -WV] [info : Mon-Info])
  (struct -FC [c : -WV] [v : -WV] [lo : Mon-Party])
  (subset: -Ans
    -blm
    -WVs))

(: -⇓ : -e -ρ → -E)
;; Close expression with restricted environment
;; and perform some simplifications to compress trivial reduction steps
(define (-⇓ e ρ)
  (match e
    [(? -v? v) (-W (list (close v ρ)) v)]
    [(-@ (and k (-st-mk id 0)) '() _) (-W (list (-St id '())) (-?@ k))]
    [_ (-↓ e (ρ↓ ρ (FV e)))]))

(define (show-E [E : -E]) : (Listof Sexp)
  (match E
    [(-↓ e ρ) `(,(show-e e) ∣ ,@(show-ρ ρ))]
    [(-Mon C V _) `(Mon ,(show-WV C) ,(show-WV V))]
    [(-FC C V _) `(FC ,(show-WV C) ,(show-WV V))]
    [(-blm l+ lo V C) `(blame ,l+ ,lo ,(show-V V) ,(map show-V C))]
    [(-W Vs e) `(,@(map show-V Vs) @ ,(show-?e e))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Continuation frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (struct -φ.set! [x : Symbol] [α : -α]) ; need both variable and address
  (struct -φ.@ [es : (Listof -E)] [vs : (Listof -WV)] [ctx : -src-loc])
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
    [mon-info : Mon-Info]
    [pos : (Option Integer)])
  (struct -φ.indy.rng
    [fun : -V] [args : (Listof -WV)] [mon-info : Mon-Info] [pos : (Option Integer)])
  (struct -φ.rt.@ [Γ : -Γ] [xs : (Listof Symbol)] [f : -?e] [args : (Listof -?e)])
  (struct -φ.rt.let [old-dom : (Setof Symbol)])
  ;; contract stuff
  (struct -φ.μc [x : Symbol] [pos : (Option Integer)])
  (struct -φ.struct/c
    [name : -id] [fields : (Listof -e)] [env : -ρ] [fields↓ : (Listof -WV)]
    [pos : (Option Integer)])
  (struct -φ.=>i
    [dom : (Listof -e)] [dom↓ : (Listof -V)] [cs↓ : (Listof -?e)] [xs : (Listof Symbol)]
    [rng : -e] [env : -ρ] [pos : (Option Integer)])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack address


;; Stack
(define-data -κ
  (struct -τ [e : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -kont [frm : -φ] [nxt : -κ]))

;; Push frames on top of existing stack
;; TODO: Make it a function. How do they type `list*`??
(define-syntax -kont*
  (syntax-rules ()
    [(_ κ) κ]
    [(_ φ₁ φ* ... κ) (-kont φ₁ (-kont* φ* ... κ))]))

;; Stack store
(define-type -Ξ (MMap -τ -kont))
(define-type -ΔΞ (ΔMap -τ -kont))

(define show-τ : (-τ → Symbol) (unique-name 'τ))

(define (show-φ [φ : -φ] [v : Sexp]) : (Listof Sexp)
  (match φ
    [(-φ.if t e) `(if ,v ,(show-E t) ,(show-E e))]
    [(-φ.let-values x bnds bnds↓ _env body _ctx)
     `(let (,@(reverse
               (for/list : (Listof Sexp) ([(x W) (in-hash bnds↓)])
                 `[,x ,(show-WV W)]))
            [,x ,v]
            ,@(for/list : (Listof Sexp) ([bnd bnds])
                (match-define (cons x e_x) bnd)
                `[,x ,(show-e e_x)]))
        ,(show-e body))]
    [(-φ.letrec-values x bnds _env body _ctx)
     `(letrec ([,x ,v]
               ,@(for/list : (Listof Sexp) ([bnd bnds])
                   (match-define (cons x e_x) bnd)
                   `[,x ,(show-e e_x)]))
        ,(show-e body))]
    [(-φ.set! x _) `(set! ,x ,v)]
    [(-φ.@ Es Ws _)
     `(,@(reverse (map show-V (map (inst -W-x -V) Ws)))
       ,v ,@(map show-E Es))]
    [(-φ.begin es _) `(begin ,@(map show-e es))]
    [(-φ.begin0v es _) `(begin0 ,v ,@(map show-e es))]
    [(-φ.begin0e (-W Vs _) es _)
     `(begin0 ,(map show-V Vs) ,@(map show-e es))]
    [(-φ.mon.v ctc _)
     `(mon ,(if (-E? ctc) (show-E ctc) (show-V (-W-x ctc))) ,v)]
    [(-φ.mon.c val _)
     `(mon ,v ,(if (-E? val) (show-E val) (show-V (-W-x val))))]
    [(-φ.indy.dom x xs cs Cs args args↓ fun rng _env _ _)
     `(indy.dom
       [,@(reverse
           (for/list : (Listof Sexp) ([arg args↓])
             (match-define (cons x W_x) arg)
             `[,x ∈ ,(show-WV W_x)]))
        (,x ,v)
        ,@(for/list : (Listof Sexp) ([x xs] [c cs] [C Cs] [arg args])
            `(mon ,(show-WV (-W C c)) ,(show-WV arg) as ,x))
        ↦ ,(show-e rng)]
       ,(show-V fun))]
    [(-φ.indy.rng fun args _ _)
     `(indy.rng (mon ,v (,(show-V fun) ,@(map show-WV args))))]
    [(-φ.rt.@ Γ xs f args)
     `(rt ,(show-Γ Γ)
          (,(show-?e f)
           ,@(for/list : (Listof Sexp) ([x xs] [arg args])
               `(,x ↦ ,(show-?e arg))))
          ,v)]
    [(-φ.rt.let dom) `(rt/let ,@(set->list dom) ,v)]
    [(-φ.μc x _) `(μ/c ,x ,v)]
    [(-φ.struct/c id cs _ρ cs↓ _)
     `(,(-id-name (id/c id))
       ,@(reverse (map show-WV cs↓))
       ,v
       ,@(map show-e cs))]
    [(-φ.=>i cs Cs↓ cs↓ xs e ρ _)
     `(=>i ,@(reverse (map show-V Cs↓)) ,v ,@(map show-e cs))]
    ))

(: show-κ ([-κ] [Sexp] . ->* . (Listof Sexp)))
(define (show-κ κ [v '□])
  (match κ
    [(? -τ? τ) `(,v ↝ ,(show-τ τ))]
    [(-kont φ κ*) (show-κ κ* (show-φ φ v))]))

(define (show-Ξ [Ξ : -Ξ]) : (Listof Sexp)
  (for/list : (Listof Sexp) ([(τ κs) Ξ])
    `(,(show-τ τ) ↦ ,@(for/list : (Listof Sexp) ([κ κs]) (show-κ κ '□)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State (narrow)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -ς ([e : -E] [Γ : -Γ] [κ : -κ] [σ : -σ] [Ξ : -Ξ] [M : -M]) #:transparent)
(struct -Δς ([e : -E] [Γ : -Γ] [κ : -κ] [δσ : -Δσ] [δΞ : -ΔΞ] [δM : -ΔM]) #:transparent)

(define-type -ς* (U -ς (Setof -ς)))
(define-type -Δς* (U -Δς (Setof -Δς)))

(: 𝑰 : -prog → -ς)
;; Load program to intial machine state
;; FIXME: allow expressions in top-levels and execute them instead,
;;        then initialize top-levels to `undefined`
(define (𝑰 p)
  (match-define (-prog ms e₀) p)

  (: alloc-es : -σ -id (Option Integer) (Listof -e) → (Values -σ (Listof -α)))
  (define (alloc-es σ id pos es)
    (define-values (σ* αs-rev)
      (for/fold ([σ* : -σ σ] [αs-rev : (Listof -α) '()])
                ([e es] [i (in-naturals)])
        (define-values (σ** V) (alloc-e σ* e))
        (define α (-α.fld id pos i))
        (values (⊔ σ** α V) (cons α αs-rev))))
    (values σ* (reverse αs-rev)))

  (: alloc-e : -σ -e → (Values -σ -V))
  (define (alloc-e σ e)
    (match e
      [(? -v?) (values σ (close-Γ -Γ⊤ (close e -ρ⊥)))]
      [(-->i doms rng pos)
       (define-values (xs cs)
         (for/lists ([xs : (Listof Symbol)] [cs : (Listof -e)])
                    ([dom doms])
           (values (car dom) (cdr dom))))
       (define-values (σ* γs) (alloc-es σ (-id-local '-> 'Λ) pos cs))
       (values σ* (-=>i xs cs γs rng -ρ⊥ -Γ⊤))]
      [(-@ (-st-mk (and t (or 'and/c 'or/c 'not/c)) _) cs (-src-loc _ pos))
       (define-values (σ* αs) (alloc-es σ t pos cs))
       (values σ* (-St t αs))]
      [(-struct/c id cs pos)
       (define-values (σ* αs) (alloc-es σ id pos cs))
       (values σ* (-St/C id αs))]
      [e (error '𝑰 "TODO: execute general expression. For now can't handle ~a"
                (show-e e))]))

  ;; Assuming each top-level variable binds a value for now.
  ;; TODO generalize.
  (define σ₀
    (for*/fold ([σ : -σ -σ⊥])
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
            (⊔ σ* (-α.def (-id-local (car ids) mod-path)) V)]
           [else
            (error '𝑰 "TODO: general top-level. For now can't handle `define-~a-values`"
                   (length ids))])]
        [(? -require?) σ]
        ;; provide
        [(-provide specs)
         (for/fold ([σ : -σ σ]) ([spec specs])
           (match-define (-p/c-item x c) spec)
           (define-values (σ₁ C) (alloc-e σ c))
           (define id (-id-local x mod-path))
           (define σ₂ (⊔ σ₁ (-α.ctc id) C))
           (cond
             [(hash-has-key? σ₂ (-α.def id)) σ₂]
             [else (⊔ σ₂ (-α.def id) '•)]))]
        ;; submodule-form
        [(? -module?) (error '𝑰 "TODO: sub-module forms")])))

  (define E₀ (-↓ e₀ -ρ⊥))
  (define τ₀ (-τ e₀ -ρ⊥ -Γ⊤))

  (-ς E₀ -Γ⊤ τ₀ σ₀ (hash τ₀ ∅) (hash)))

(: final? (case-> [-ς → Boolean]
                  [-E -κ -Ξ → Boolean]))
;; Check whether state is final
(define final?
  (case-lambda
    [(E κ Ξ)
     (and (-τ? κ)
          (set-empty? (hash-ref Ξ κ))
          (-Ans? E))]
    [(ς)
     (match-define (-ς E _ κ _ Ξ M) ς)
     (final? E κ Ξ)]))

(define (show-ς [ς : -ς]) : (Listof Sexp)
  (match-define (-ς E Γ κ σ Ξ M) ς)
  `((E: ,@(show-E E))
    (Γ: ,@(show-Γ Γ))
    (κ: ,@(show-κ κ '□))
    (σ: ,@(show-σ σ))
    (Ξ: ,@(show-Ξ Ξ))
    (M: ,@(show-M M))))
