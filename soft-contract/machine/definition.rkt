#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "../utils/def.rkt" "../utils/pretty.rkt" "../utils/map.rkt" "../utils/set.rkt" "../utils/non-det.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "../parse/main.rkt"
 "../runtime/env.rkt" "../runtime/val.rkt" "../runtime/path-inv.rkt" "../runtime/addr.rkt"
 "../runtime/store.rkt" "../runtime/summ.rkt")

(provide (all-defined-out))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Closure forms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-data -E
  (struct -↓ [e : -e] [ρ : -ρ])
  ; `V` and `e` don't have any reference back to `E`, so it's not recursive
  (struct -Mon [c : -WV] [v : -WV] [info : Mon-Info] [pos : Integer])
  (struct -App [f : -WV] [xs : (Listof -WV)] [ctx : -src-loc])
  -define-values
  -provide
  (subset: -Ans
    -blm
    -WVs))

(: -⇓ : -e -ρ → -E)
;; Close expression with restricted environment
;; and perform some simplifications to compress trivial reduction steps
(define (-⇓ e ρ)
  (match e
    [(? -v? v) (-W (list (close v ρ)) v)]
    [(-@ (and k (-st-mk (and s (-struct-info _ 0 _)))) '() _)
     (-W (list (-St s '())) (-@ k (list) -Λ))]
    [_ (-↓ e (ρ↓ ρ (FV e)))]))

(define (show-E [E : -E]) : (Listof Sexp)
  (match E
    [(-↓ e ρ) `(,(show-e e) ∣ ,@(show-ρ ρ))]
    [(-Mon C V _ _) `(Mon ,(show-WV C) ,(show-WV V))]
    [(-App F Vs _) `(App ,(show-WV F) ,@(map show-WV Vs))]
    [(-define-values _ xs e) `(define-values xs ,(show-e e))]
    [(-provide _ items)
     `(provide ,@(for/list : (Listof Sexp) ([i items])
                   (match-let ([(-p/c-item x c) i])
                     `(,x ,(show-e c)))))]
    [(-blm l+ lo V C) `(blame ,l+ ,lo ,(show-V V) ,(map show-V C))]
    [(-W Vs e) `(,@(map show-V Vs) @ ,(show-?e e))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Continuation frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-data -φ

  ;; Standard stuff
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

  ;; Top-level stuff
  (struct -φ.top [items : (Listof (U -define-values -provide))] [e : -e])
  (struct -φ.def [path : Adhoc-Module-Path] [xs : (Listof Symbol)])
  (struct -φ.ctc [path : Adhoc-Module-Path] [items : (Listof -p/c-item)] [current : Symbol])

  ;; Represent next steps for contract checking
  (struct -φ.mon.v [ctc : (U -E -WV)] [mon-info : Mon-Info] [pos : Integer])
  (struct -φ.mon.c [val : (U -E -WV)] [mon-info : Mon-Info] [pos : Integer])
  (struct -φ.indy.dom
    [pending : Symbol] ; variable for next current expression under evaluation
    [args : (Listof (List Symbol -WV -WV))] ; remaining contracts and arguments to monitor
    [args↓ : (Listof (Pairof Symbol -WV))] ; evaluated arguments, reversed
    [Rst : (Option (List Symbol -WV (Listof -WV)))] ; rest of varargs
    [fun : -V] ; inner function
    [rng : -e] ; range
    [env : -ρ] ; range's context
    [mon-info : Mon-Info]
    [pos : Integer])
  (struct -φ.indy.rst
    [pending : Symbol] ; variable for varargs
    [args : (Listof (Pairof Symbol -WV))] ; init, monitored arguments, in right order
    [fun : -V] ; inner function
    [rng : -e] ; range
    [env : -ρ] ; range's context
    [mon-info : Mon-Info]
    [pos : Integer])
  (struct -φ.indy.rng
    [fun : -V] [args : (Listof -WV)] [rst : (Option -WV)] [mon-info : Mon-Info] [pos : Integer])
  (struct -φ.mon.struct
    [info : -struct-info] [ctcs : (Listof -α)] [cs : (Listof -?e)] [idx : Integer]
    [vals↓ : (Listof -WV)] [target : -WV] [mon-info : Mon-Info] [pos : Integer])
  (struct -φ.mon.vector/c ; no need to accumulated checked fields. Vector always wraps.
    [ctcs : (Listof -α)] [cs : (Listof -?e)] [idx : Integer]
    [target : -WV] [mon-info : Mon-Info] [pos : Integer])
  (struct -φ.mon.vectorof
    [ctc : -WV] [len : Integer] [idx : Integer]
    [target : -WV] [mon-info : Mon-Info] [pos : Integer])

  ;; Accumulate higher-order contracts with passing first-order checks
  (struct -φ.filter-fo
    [queue : (Listof -WV)] [passed : (Listof -WV)] [current : -WV] [value : -WV]
    [mon-info : Mon-Info] [pos : Integer])
  
  ;; Represent next step for escaping from a block
  (struct -φ.rt.@ [Γ : -Γ] [xs : -formals] [f : -?e] [args : (Listof -?e)])
  (struct -φ.rt.let [old-dom : (Setof Symbol)])
  
  ;; contract stuff
  (struct -φ.μ/c [pos : Integer])
  (struct -φ.struct/c
    [info : -struct-info] [fields : (Listof -e)] [env : -ρ] [fields↓ : (Listof -WV)]
    [pos : Integer])
  (struct -φ.=>i
    [dom : (Listof -e)]
    [dom↓ : (Listof -WV)]
    [xs : (Listof Symbol)]
    [rst : (U #f #|no rest|#
              (Pairof Symbol -e) #|unevaluated|#
              Symbol #|pending|#)]
    [rng : -e] [env : -ρ] [pos : Integer])
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    [(-φ.mon.v ctc _ _)
     `(mon ,(if (-E? ctc) (show-E ctc) (show-V (-W-x ctc))) ,v)]
    [(-φ.mon.c val _ _)
     `(mon ,v ,(if (-E? val) (show-E val) (show-V (-W-x val))))]
    [(-φ.indy.dom x args args↓ Rst fun rng _env _ _)
     (define show-Rst
       (match Rst
         [(list x* WC* WVs)
          `(#:rest (mon ,(show-WV WC*) (list ,@(map show-WV WVs)) as ,x*))]
         [#f '()]))
     `(indy.dom
       [,@(reverse
           (for/list : (Listof Sexp) ([arg args↓])
             (match-define (cons x W_x) arg)
             `[,x ∈ ,(show-WV W_x)]))
        (,x ,v)
        ,@(for/list : (Listof Sexp) ([arg : (List Symbol -WV -WV) args])
            (match-define (list x WC WV) arg)
            `(mon ,(show-WV WC) ,(show-WV WV) as ,x))
        ,@show-Rst
        ↦ ,(show-e rng)]
       ,(show-V fun))]
    [(-φ.indy.rng fun args rst _ _)
     (define show-rst
       (cond
         [rst `(#:rest ,(show-WV rst))]
         [else '()]))
     `(indy.rng (mon ,v (,(show-V fun) ,@(map show-WV args) ,@show-rst)))]
    [(-φ.mon.struct s γs _cs i Ws↓ _ _ _)
     (match-define-values (γs-done (cons γ-cur γs-left)) (split-at γs i))
     `(mon/struct/c
       (,@(for/list : (Listof Sexp) ([γ γs-done]) `(,(show-α γ) ▹ ✓))
        (,(show-α γ-cur) ,v)
        ,@(for/list : (Listof Sexp) ([γ γs-left]) `(,(show-α γ) ▹ ??))))]
    [(-φ.mon.vector/c γs _ i _ _ _)
     (match-define-values (γs-done (cons γ-cur γs-left)) (split-at γs i))
     `(mon/vector/c
       ,@(for/list : (Listof Sexp) ([γ γs-done]) `(,(show-α γ) ▹ ✓))
       (,(show-α γ-cur) ,v)
       ,@(for/list : (Listof Sexp) ([γ γs-left]) `(,(show-α γ) ▹ ??)))]
    [(-φ.mon.vectorof Wc n i _ _ _)
     `(mon/vectorof ,(show-V (-W-x Wc)) (... ,v ...))]
    [(-φ.rt.@ Γ xs f args)
     (define (show-bnds [xs : (Listof Symbol)] [args : (Listof -?e)]) : (Listof Sexp)
       (for/list : (Listof Sexp) ([x xs] [arg args])
         `(,x ↦ ,(show-?e arg))))
     
     (define bnds
       (match xs
         [(? list? xs) (show-bnds xs args)]
         [(-varargs zs z)
          (define-values (args-init args-rest) (split-at args (length zs)))
          `(,@(show-bnds zs args-init) `(,z ↦ ,(map show-?e args-rest)))]))
     
     `(rt ,(show-Γ Γ) (,(show-?e f) ,@bnds) ,v)]
    [(-φ.rt.let dom) `(rt/let ,@(set->list dom) ,v)]
    [(-φ.μ/c x) `(μ/c ,(show-x/c x) ,v)]
    [(-φ.struct/c s cs _ρ cs↓ _)
     `(,(show/c (show-struct-info s))
       ,@(reverse (map show-WV cs↓))
       ,v
       ,@(map show-e cs))]
    [(-φ.=>i cs WCs↓ xs rst e ρ _)
     (match rst
       [#f
        `(=>i ,@(reverse (map show-WV WCs↓)) ,v ,@(map show-e cs))]
       [(? symbol?)
        `(=>i* ,@(reverse (map show-WV WCs↓)) ,@(map show-e cs) #:rest [,rst ,v])]
       [(cons x* e*)
        `(=>i* ,@(reverse (map show-WV WCs↓)) ,v ,@(map show-e cs) #:rest [,x* ,(show-e e*)])])]
    [(-φ.top itms e)
     `(,@(map show-module-level-form itms) ,(show-e e))]
    [(-φ.def _ xs) `(define-values ,xs ,v)]
    [(-φ.ctc _ itms x)
     `(provide
       ,@(map show-provide-spec itms)
       [,x ,v])]
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

(: with-Δ : -Δσ -ΔΞ -ΔM -Δς* → -Δς*)
;; Append store deltas to given state delta
(define (with-Δ δσ δΞ δM δς)
  (match/nd: (-Δς → -Δς) δς
    [(-Δς E Γ κ δσ* δΞ* δM*)
     (-Δς E Γ κ (append δσ δσ*) (append δΞ δΞ*) (append δM δM*))]))

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
