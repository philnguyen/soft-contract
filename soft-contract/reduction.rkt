#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt" "delta.rkt" "machine.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

(provide (all-defined-out)) ; TODO

(: ↦ : -prog → (-ς → -ς*))
;; Steps a full state in the CEΓKSΞ machine
(define (↦ p)
  (match-define (-prog ms e†) p)
  (define τ₀ (-τ (-↓ e† -ρ∅) -Γ∅)) ;; the `mt` continuation pointer

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

  (: ↦mon : -WV -WV (Setof Symbol) -Γ -τ -σ -Ξ -M Mon-Info → -ς)
  ;; Stepping rules for contract monitoring
  (define (↦mon W_c W_v xs Γ τ σ Ξ M l³)
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

  (: -ς/pushed : -e -ρ -Γ -φ -τ -σ -Ξ -M → -ς)
  ;; Proceed to the next `eval` state with given frame `φ` pushed
  (define (-ς/pushed e ρ Γ φ τ σ Ξ M)
    (define FVs (FV e))
    (define ρ* (ρ↓ ρ FVs))
    (define Γ* (Γ↓ Γ FVs))
    (define E* (-↓ e ρ*))
    (define τ* (-τ E* Γ*))
    (define Ξ* (⊔ Ξ τ* (-κ φ τ)))
    (-ς E* Γ τ* σ Ξ* M)) ; important not to restrict `Γ` for precision

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
            (↦mon (-W C #f) (-W V ref) (dom ρ) Γ τ σ Ξ M (list ctx* ctx ctx*)))])]
      ;; evaluate function position, pushing arguments
      [(-@ f xs l)
       (define Es : (Listof -E)
         (for/list ([x xs]) (-⇓ x ρ)))
       (define φ (-φ.@ Es '() l))
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

  (: ↦WVs : -WVs -Γ -φ -τ -σ -Ξ -M → -ς*)
  ;; Stepping rules for "apply" states
  (define (↦WVs W Γ φ τ σ Ξ M)
    (match-define (-W Vs ?e) W)
    ;; Leave `M` alone for now. TODO: update it.
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
       (cond
         ;; Make sure arity is right
         [(= n (length Vs))
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
             (-ς/pushed e* ρ Γ φ* τ σ Ξ M)])]
         [else (-ς (-blm/arity l 'let-values n Vs) Γ τ σ Ξ M)])]
      ;; letrec-values
      #;[(-φ.letrec-values xs bnds ρ e l old-dom)
       (define n (length xs))
       ;; make sure the arity is right
       (cond
         [(= n (length Ws))
          (match bnds
            ;; proceed to letrec's body
            ['()
             (define τ* (τ↓ e ρ Γ))
             (define κ* (-κ (-φ.rt old-dom Γ) τ))
             (define Ξ* (⊔ Ξ τ* κ*))
             (-ς (-↓ e ρ) Γ τ* σ Ξ* M)]
            ;; proceed to next assigning clause
            [(cons (cons xs* e*) bnds*)
             (define-values (Γ* σ*)
               (for/fold ([Γ* : -Γ Γ] [σ* : -σ σ]) ([x xs] [W Ws])
                 (define α (ρ@ ρ x))
                 (match-define (-W V π) W)
                 (values (Γ+ Γ* (-π@* 'equal? (list (-x x) π)))
                         (⊔ σ* α V))))
             (define τ* (τ↓ e* ρ Γ*))
             (define κ* (-κ (-φ.letrec-values xs* bnds* ρ e l old-dom) τ))
             (define Ξ* (⊔ Ξ τ* κ*))
             (-ς (-↓ e* ρ) Γ* τ* σ* Ξ* M)])]
         [else (-ς (-W (-blm/arity l 'letrec-values n Ws) #f) Γ τ₀ σ Ξ M)])]
      ;; Application
      #;[(-φ.@ Es WVs ρ l)
       (match Ws
         [(list W)
          (match Es
            ;; Evaluate body with extended environments, remembering to restore fact environment later
            ['()
             (match-define (cons W_f W_xs) (reverse (cons W WVs)))
             (↦@ W_f W_xs ρ Γ τ σ Ξ M l)]
            ;; Swap next argument for evaluation
            [(cons E Es*)
             (define τ*
               (match E
                 [(-↓ e ρ) (τ↓ e ρ Γ)]
                 [_ (-τ E Γ)]))
             (define κ* (-κ (-φ.@ Es* (cons W WVs) ρ l) τ))
             (define Ξ* (⊔ Ξ τ* κ*))
             (-ς E Γ τ* σ Ξ* M)])]
         [_ (-ς (-W (-blm/arity l 'apply 1 Ws) #f) Γ τ₀ σ Ξ M)])]
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
      #;[(-φ.mon ce xs (and l³ (list l₊ l₋ lₒ)))
       (match Ws
         [(list W)
          (match ce
            [(cons #f (? -E? E))
             (define τ* (τ↓ E Γ))
             (define κ* (-κ (-φ.mon ((inst cons -WV #f) W #f) xs l³) τ))
             (define Ξ* (⊔ Ξ τ* κ*))
             (-ς E Γ τ* σ Ξ* M)]
            [(cons (? -W? W_c) #f)
             (↦mon W_c W xs Γ τ σ Ξ M l³)])]
         [_ (-ς (-W (-blm/arity l₊ lₒ 1 Ws) #f) Γ τ σ Ξ M)])]
      ;; indy
      #;[(-φ.indy W_cs W_xs W_xs↓ rng (list l₊ l₋ lₒ))
       (match Ws
         [(list W)
          (error '↦WVs "TODO: indy")]
         [_ (-ς (-W (-blm/arity l₊ lₒ 1 Ws) #f) Γ τ σ Ξ M)])]
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
      #;[(-φ.=>i cs cs↓ xs rng ρ)
       (match Ws
         [(list (-W V _))
          (define cs↓* (cons V cs↓))
          (define n (length cs↓*))
          (match cs
            ['()
             (define-values (αs σ*)
               ;; accumulate new store and address list for contract domains
               ;; (domains are reversed compared to `cs↓*`)
               (for/fold ([αs : (Listof -α) '()] [σ* : -σ σ])
                         ([V cs↓*] [i (in-naturals)])
                 (define α (alloc -ff #|TODO dummy|# '=>i (- n i 1) Γ))
                 (values (cons α αs) (⊔ σ* α V))))
             (define W_c (-W (-=>i (map (inst cons Symbol -α) xs αs) rng ρ Γ) #f))
             (-ς (list W_c) Γ τ σ* Ξ M)]
            [(cons c cs*)
             (define τ* (τ↓ c ρ Γ))
             (define κ* (-κ (-φ.=>i cs* cs↓* xs rng ρ) τ))
             (define Ξ* (⊔ Ξ τ* κ*))
             (-ς (-↓ c ρ) Γ τ* σ Ξ* M)])]
         [else (error '↦WVs "TODO: catch arity error for -->i")])]
      ))
  
  (match-lambda
   [(-ς (-↓ e ρ) Γ τ σ Ξ M) (↦e e ρ Γ τ σ Ξ M)]
   [(-ς (? -W? W) Γ τ σ Ξ M)
    (match/nd: (-κ → -ς) (hash-ref Ξ τ)
      [(-κ φ τ*) (↦WVs W Γ φ τ* σ Ξ M)])]
   [ς (error '↦ "unexpected: ~a" ς)]))

(: -blm/arity : Mon-Party Mon-Party Integer -Vs → -blm)
;; Create error message that blames given party for using the wrong number of values
(define (-blm/arity l₊ lₒ n Vs)
  (-blm l₊ lₒ
        (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) 'Λ) -ρ∅ -Γ∅)
        Vs))
