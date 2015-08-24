#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt" "delta.rkt" "machine.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(provide (all-defined-out)) ; TODO

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
        (for/set: : (Setof -ς) ([V (σ@ σ α)] #:unless (spurious? Γ x V))
          (-ς (-W (list V) x) Γ τ σ Ξ M))])]
    ;; look up top-level reference
    [(and ref (-ref (and id (-id name ctx*)) ctx))
     (cond
       ;; skip contract checking for self reference
       [(equal? ctx ctx*)
        (for/set: : (Setof -ς) ([V (σ@ σ (-α.def id))])
          (-ς (-W (list V) ref) Γ τ σ Ξ M))]
       ;; perform contract checking for cross-module reference
       [else
        (for*/set: : (Setof -ς) ([V (σ@ σ (-α.def id))]
                                 [C (σ@ σ (-α.ctc id))])
          (↦mon (-W C #f) (-W V ref) Γ τ σ Ξ M (list ctx* ctx ctx*)))])]
    ;; evaluate function position, pushing arguments
    [(-@ f xs l)
     (define φ (-φ.@ xs (ρ↓ ρ (FV xs)) '() l))
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
        (define φ (-φ.let-values xs bnds* (hash) ρ e l))
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
    ;; @-havoc
    [(-@-havoc x)
     (match/nd: (-V → -ς) (σ@ σ (ρ@ ρ x))
                [(and V (-Clo xs _ ρ Γ))
                 (define n
                   (match xs
                     [(? list?) (length xs)]
                     [(-varargs zs _) (+ 1 (length zs))]))
                 (↦@ (-W V #f) (make-list n -●) ρ Γ τ σ Ξ M ☠)]
                [(and V (-Ar γ _ l³))
                 (match/nd: (-V → -ς) (σ@ σ γ)
                            [(-=>  cs _    ) (↦@ (-W V #f) (make-list (length cs) -●) ρ Γ τ σ Ξ M ☠)]
                            [(-=>i cs _ _ _) (↦@ (-W V #f) (make-list (length cs) -●) ρ Γ τ σ Ξ M ☠)])])]
    ;; amb
    [(-amb es)
     (for/set: : (Setof -ς) ([e es])
       (-ς (-⇓ e ρ) Γ τ σ Ξ M))]
    ;; contract stuff
    [(-μ/c x c)
     (error '↦e "TODO: μ/c")]
    [(--> cs d)
     (match cs
       ['()
        (define φ (-φ.=> '() '() ρ))
        (-ς/pushed d ρ Γ φ τ σ Ξ M)]
       [(cons c cs*)
        (define φ (-φ.=> (append cs* (list d)) '() ρ))
        (-ς/pushed c ρ Γ φ τ σ Ξ M)])]
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

(: ↦@ : -WV (Listof -WV) -ρ -Γ -τ -σ -Ξ -M Mon-Party → -ς*)
;; Stepping rules for function application
(define (↦@ W_f W_xs ρ Γ τ σ Ξ M l)
  (error '↦@ "TODO")
  #|
  (match-define (-W V_f π_f) W_f)
  (define-values (V_xs π_xs)
  (for/lists ([V_xs : (Listof -V)] [π_xs : (Listof -π*)])
  ([W W_xs])
  (values (-W-x W) (-W-π W))))
  (match V_f
  [(? -o? o)
  (define-values (σ* AΓs) (δ σ Γ o W_xs l))
  (define π_a (-π@* π_f π_xs))
  (match/nd: (-AΓ → -ς) AΓs
  [(-AΓ (? -blm? blm) Γ*)
  (-ς (-W blm π_a) Γ* τ σ Ξ M)]
  [(-AΓ (list V) Γ*)
  (-ς (list (-W V π_a)) Γ* τ σ Ξ M)])]
  [(-Clo xs e ρ* Γ*)
  (match xs
  [(? list? xs)
  
  (: πx→x : -π* → -π*)
  ;; Convert a fact about existing arguments into one about parameters
  (define (πx→x π)
  (for/fold ([π π]) ([x xs] [π_x π_xs])
  (π*/ π π_x (-x x))))

  ;; Check whether converted fact is relevant
  (define relevant-π?
  (let ([xs* : (Setof Symbol) (list->set xs)])
  (λ ([π : -π*]) (⊆ (FV-π π) xs*))))

  ;; for each binding [x ↦ π],
  ;; turn each relevant fact about `π` in `Γ` to one about `x` in `Γ*`
  (define Γ**
  (for*/fold ([Γ** : -Γ Γ*])
  ([π Γ] [π* (in-value (πx→x π))] #:when (relevant-π? π*))
  (Γ+ Γ** π*)))

  (define-values (ρ** σ*)
  (for/fold ([ρ** : -ρ ρ*] [σ* : -σ σ])
  ([x xs] [V_x V_xs])
  (define α (alloc e x Γ)) ; monovariant for now
  (values (ρ+ ρ** x α) (⊔ σ* α V_x))))
  
  (define τ* (τ↓ e ρ** Γ**))
  (define κ* (-κ (-φ.rt@ (dom ρ) π_f xs π_xs) τ))
  (define Ξ* (⊔ Ξ τ* κ*))
  (-ς (-↓ e ρ**) Γ** τ* σ* Ξ* M)]
  [(-varargs zs z)
  (error '↦@ "TODO: varargs")])]
  ['•
  (error '↦@ "TODO: •")]
  [_ (-ς (-W (-blm l 'apply 'procedure? (list V_f)) #f) Γ τ σ Ξ M)])
  |#)

(: ↦mon : -WV -WV -Γ -τ -σ -Ξ -M Mon-Info → -ς)
;; Stepping rules for contract monitoring
(define (↦mon W_c W_v Γ τ σ Ξ M l³)
  (error '↦mon "TODO")
  #|
  (match-define (-W V_c π_c) W_c)
  (match-define (-W V   π  ) W_v)
  (match-define (list l₊ l₋ lₒ) l³)
  (match (⊢ σ Γ W_v W_c)
  ['✓ (-ς (list W_v) Γ τ σ Ξ M)]
  ['X (-ς (-W (-blm l₊ lₒ V_c (list V)) #f) Γ τ σ Ξ M)]
  ['?
  (match V_c
  [(-=> doms rng)
  (error '↦mon "->")]
  [(-=>i doms rng ρ_c Γ_c)
  (error '↦mon "->i")]
  [(-St/C id cs)
  (error '↦mon "struct/c")]
  [(-μ/C x c)
  (error '↦mon "μ/c")]
  [(-X/C x)
  (error '↦mon "ref")]
  [_
  (error '↦mon "TODO: flat")])])
  |#)

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
        (define-values (Γ_t Γ_f) (split-Γ Γ V ?e))
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
                      (Γ+ Γ* (-?@ 'equal? (list (-x x) ex)))
                      (⊔ σ* α V))))
          (define φ* (-φ.rt.dom (dom ρ)))
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
                   (Γ+ Γ* (-?@ 'equal? (list (-x x) ex)))
                   (⊔ σ* α V))))
       (match bnds
         ;; proceed to letrec's body
         ['()
          (define φ* (-φ.rt.dom dom₀))
          (-ς/pushed e ρ* Γ* φ* τ σ* Ξ M)]
         ;; proceed to next assigning clause
         [(cons (cons xs* e*) bnds*)
          (define φ* (-φ.letrec-values xs* bnds* ρ e l dom₀))
          (-ς/pushed e* ρ* Γ* φ* τ σ* Ξ M)]))]
    ;; Application
    [(-φ.@ es ρ WVs l)
     (with-guarded-arity 1 l 'apply
       (match-define (list V) Vs)
       (define WVs* (cons (-W V ?e) WVs))
        (match es
          ['()
           (match-define (cons W_f W_xs) (reverse WVs*))
           (↦@ W_f W_xs ρ Γ τ σ Ξ M l)]
          ;; Swap next argument for evaluation
          [(cons e* es*)
           (define φ* (-φ.@ es* (ρ↓ ρ (FV es*)) WVs* l))
           (-ς/pushed e* ρ Γ φ* τ σ Ξ M)]))]
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
    [(-φ.indy W_cs W_xs W_xs↓ rng (list l+ l- lo))
     (with-guarded-arity 1 l+ lo
       (error '↦WVs "TODO: indy"))]
    ;; restore fact environment
    [(-φ.rt Γ₀ e₀)
     (cond
       [(spurious? Γ₀ e₀ Vs)
        (log-debug "rt: eliminate spurious result ~a for ~a knowing ~a~n"
                   (show-Vs σ Vs) (and e₀ (show-e σ e₀)) (show-Γ Γ₀))
        ∅]
       [else (-ς (-W Vs e₀) Γ₀ τ σ Ξ M)])]
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
    [(-φ.=> cs Cs ρ)
     (match Vs
       [(list V)
        (define Cs* (cons (-W V ?e) Cs))
        (define n (length Cs*))
        (match cs
          [(list)
           (define-values (αs σ* es*)
             ; accumulate new store and address list
             ; which is reversed compared to `Cs*`, hence of the right order
             (for/fold ([αs : (Listof -α) '()] [σ* : -σ σ] [es* : (Listof -?e) '()])
                       ([C Cs*] [i (in-range n)])
               (match-define (-W V e) C)
               (define α
                 (cond [e (-α.val e)]
                       [else (-α.opq (-id '-> 'Λ) #f #|TODO|# i)]))
               (values (cons α αs)
                       (⊔ σ* α V)
                       (cons e es*))))
           (match-define-values (α-doms (list α-rng)) (split-at αs (- n 1)))
           (match-define-values (e-doms (list e-rng)) (split-at es* (- n 1)))
           (define C (-=> α-doms α-rng))
           (define e_C (-?-> e-doms e-rng))
           (-ς (-W (list C) e_C) Γ τ σ Ξ M)]
          [(cons c cs*)
           (define φ* (-φ.=> cs* Cs* ρ))
           (-ς/pushed c ρ Γ φ* τ σ Ξ M)])]
       [else (error '↦WVs "TODO: catch arity error for -->")])]
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

(: ↦ : -ς → -ς*)
;; Steps a full state in the CEΓKSΞ machine
(define ↦
  (match-lambda
    [(-ς (-↓ e ρ) Γ τ σ Ξ M) (↦e e ρ Γ τ σ Ξ M)]
    [(-ς (? -W? W) Γ τ σ Ξ M)
     (match/nd: (-κ → -ς) (hash-ref Ξ τ)
                [(-κ φ τ*) (↦WVs W Γ φ τ* σ Ξ M)])]
    [ς (error '↦ "unexpected: ~a" ς)]))
