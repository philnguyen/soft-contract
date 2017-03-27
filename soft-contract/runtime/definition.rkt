#lang typed/racket/base

(provide (except-out (all-defined-out) -not/c -not/c/simp)
         (rename-out [-not/c/simp -not/c]))

(require racket/match
         racket/set
         racket/string
         racket/splicing
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Symbol ⟪α⟫))
(define-type -Δρ -ρ)
(define ⊥ρ : -ρ (hasheq))
(define (ρ@ [ρ : -ρ] [x : Symbol]) : ⟪α⟫
  (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
(define ρ+ : (-ρ Symbol ⟪α⟫ → -ρ) hash-set)

;; HACK for distinguishing allocation contexts between 0-arg thunks,
;; which is important if the thunk returns different values (e.g. vector)
;; for different contexts
(define -x-dummy (+x! 'dummy))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Store maps each address to value set and whether it may have been mutated

(define-type -cardinality (U 0 1 'N))
(struct -σ ([m : (HashTable ⟪α⟫ (℘ -V))]
            [modified : (℘ ⟪α⟫)] ; addresses that may have been mutated
            [cardinality : (HashTable ⟪α⟫ -cardinality)]
            )
  #:transparent)

(: cardinality+ : -cardinality → -cardinality)
(define (cardinality+ c)
  (case c
    [(0) 1]
    [(1) 'N]
    [else 'N]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -κ ([cont : -⟦k⟧]    ; rest of computation waiting on answer
            [pc : (℘ -t)]        ; path-condition to use for rest of computation
            [⟪ℋ⟫ : -⟪ℋ⟫]    ; abstraction of call history
            [args : (Listof -?t)])
  #:transparent)

(define-type -σₖ (HashTable -αₖ (℘ -κ)))

(define ⊥σₖ : -σₖ (hash))

(: σₖ@ : (U -Σ -σₖ) -αₖ → (℘ -κ))
(define (σₖ@ m αₖ)
  (hash-ref (if (-Σ? m) (-Σ-σₖ m) m) αₖ →∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (HashTable -αₖ (℘ -ΓA)))
(define ⊥M : -M (hash))

(: M@ : (U -Σ -M) -αₖ → (℘ -ΓA))
(define (M@ m αₖ) (hash-ref (if (-Σ? m) (-Σ-M m) m) αₖ →∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Grouped reference to mutable stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -Σ ([σ : -σ] [σₖ : -σₖ] [M : -M]) #:mutable #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . -prim
            (-● (℘ -h))
            (-St -𝒾 (Listof ⟪α⟫))
            (-Vector (Listof ⟪α⟫))
            (-Vector^ [content : ⟪α⟫] [length : #|restricted|# -V])
            -Fn
            
            ;; Proxied higher-order values
            ;; Inlining the contract in the data definition is ok
            ;; because there's no recursion
            (-Ar [guard : -=>_] [v : ⟪α⟫] [ctx : -l³])
            (-St* [guard : -St/C] [val : ⟪α⟫] [ctx : -l³])
            (-Vector/guard [guard : (U -Vector/C -Vectorof)] [val : ⟪α⟫] [ctx : -l³])
            
            -C)

(-Fn . ::= . (-Clo -formals -⟦e⟧ -ρ -Γ)
             (-Case-Clo (Listof (Pairof (Listof Symbol) -⟦e⟧)) -ρ -Γ))

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean]
                    [l : (Pairof ⟪α⟫ ℓ)]
                    [r : (Pairof ⟪α⟫ ℓ)])
            (-Or/C [flat? : Boolean]
                   [l : (Pairof ⟪α⟫ ℓ)]
                   [r : (Pairof ⟪α⟫ ℓ)])
            (-Not/C (Pairof ⟪α⟫ ℓ))
            (-One-Of/C (Listof Base)) ; Special construct for performance reason
            (-x/C [c : ⟪α⟫])
            ;; Guards for higher-order values
            -=>_
            (-St/C [flat? : Boolean]
                   [id : -𝒾]
                   [fields : (Listof (Pairof ⟪α⟫ ℓ))])
            (-Vectorof (Pairof ⟪α⟫ ℓ))
            (-Vector/C (Listof (Pairof ⟪α⟫ ℓ))))

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (-maybe-var (Pairof ⟪α⟫ ℓ))] [rng : (Pairof ⟪α⟫ ℓ)] [pos : ℓ])
              (-=>i [doms : (Listof (Pairof ⟪α⟫ ℓ))]
                    [mk-rng : (List -Clo -λ ℓ)]
                    [pos : ℓ])
              (-Case-> (Listof (Pairof (Listof ⟪α⟫) ⟪α⟫)) [pos : ℓ]))

(struct -blm ([violator : -l]
              [origin : -l]
              [c : (Listof (U -V -v -h))]
              [v : (Listof -V)]
              [loc : ℓ]) #:transparent)
(struct -W¹ ([V : -V] [t : -?t]) #:transparent)
(struct -W ([Vs : (Listof -V)] [t : -?t]) #:transparent)
(-A . ::= . -W -blm)
(struct -ΓA ([cnd : -Γ] [ans : -A]) #:transparent)

(define ⟪α⟫ℓ->⟪α⟫ (inst car ⟪α⟫ ℓ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; First order term for use in path-condition
(-t . ::= . -x
            -𝒾
            -v
            (-t.@ -h (Listof -t)))
;; Formula "head" is either a primitive operation or a stack address
(-h . ::= . -o
            -αₖ
            ;; Hacky stuff
            -One-Of/C
            (-st/c.mk -𝒾)
            (-st/c.ac -𝒾 Index)
            (-->i.mk)
            (-->i.dom Index)
            (-->i.rng)
            (-->.mk)
            (-->*.mk)
            (-->.dom Index)
            (-->.rst)
            (-->.rng)
            (-ar.mk)
            (-ar.ctc)
            (-ar.fun)
            (-values.ac Index)
            (-≥/c Base)
            (-≤/c Base)
            (->/c Base)
            (-</c Base)
            (-≡/c Base)
            (-≢/c Base)
            (-not/c -o))
(-?t . ::= . -t #f)

(define-match-expander -not/c/simp
  (syntax-rules ()
    [(_ p) (-not/c p)])
  (syntax-rules ()
    [(_ p) (case p
             [(negative?) (-≥/c 0)]
             [(    zero?) (-≢/c 0)]
             [(positive?) (-≤/c 0)]
             [else (-not/c p)])]))

(: h-unique? : -h → Boolean)
(define (h-unique? h)
  (with-debugging/off ((u?) (match h
    [(-ℬ xs _ ρ)
     (set-empty? (set-remove (set-subtract (list->seteq (hash-keys ρ))
                               (formals->names xs))
                             -x-dummy))]
    [_ #|be careful when I have new stuff|# #t]))
    (printf "h-unique? ~a : ~a~n" (show-h h) u?)))

(: t-unique? : -t → Boolean)
;; Check if term definiltey stands for a unique value.
;; `#f` is a conservative result of "maybe no"
(define (t-unique? t)
  (match t
    [(or (? -x?) (? -𝒾?) (? -v?)) #t]
    [(-t.@ h ts)
     (and (h-unique? h) (andmap t-unique? ts))]))

(: t-contains? : -t -t → Boolean)
(define (t-contains? t t*)
  (let go ([t : -t t])
    (match t
      [t #:when (equal? t t*) #t]
      [(-t.@ _ ts) (ormap go ts)]
      [_ #f])))

(: t-contains-any? : -t (℘ -t) → Boolean)
(define (t-contains-any? t ts)
  (let go ([t : -t t])
    (match t
      [t #:when (∋ ts t) #t]
      [(-t.@ _ ts) (ormap go ts)]
      [_ #f])))

(: has-abstraction? : -t → Boolean)
(define has-abstraction?
  (match-lambda
    [(-t.@ h ts)
     (or (-αₖ? h) (ormap has-abstraction? ts))]
    [_ #f]))

;; Path condition is set of terms known to have evaluated to non-#f
;; It also maintains a "canonicalized" symbolic name for each variable
(struct -Γ ([facts : (℘ -t)]
            [aliases : (HashTable Symbol -t)])
  #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq)))

(: -Γ-with-aliases : -Γ Symbol -?t → -Γ)
(define (-Γ-with-aliases Γ x ?t)
  (if ?t
      (match-let ([(-Γ ts as) Γ])
        (-Γ ts (hash-set as x ?t)))
      Γ))

(-special-bin-o . ::= . '> '< '>= '<= '= 'equal? 'eqv? 'eq? #|made up|# '≢)

(: bin-o->h : -special-bin-o → Base → -h)
(define (bin-o->h o)
  (case o
    [(>) ->/c]
    [(<) -</c]
    [(>=) -≥/c]
    [(<=) -≤/c]
    [(= equal? eqv? eq?) -≡/c]
    [(≢) -≢/c]))

(: flip-bin-o : -special-bin-o → -special-bin-o)
;; Returns o* such that (o l r) ↔ (o* r l)
(define (flip-bin-o o)
  (case o
    [(<) '>]
    [(>) '<]
    [(>=) '<=]
    [(<=) '>=]
    [else o]))

(: neg-bin-o : -special-bin-o → -special-bin-o)
;; Returns o* such that (o l r) ↔ (not (o* l r))
(define (neg-bin-o o)
  (case o
    [(<) '>=]
    [(>) '<=]
    [(>=) '<]
    [(<=) '>]
    [(= equal? eqv? eq?) '≢]
    [(≢) 'equal?]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes monitor + call site
(struct -ℒ ([mons : (℘ ℓ)] [app : ℓ]) #:transparent)

(: unpack-ℒ : -ℒ → (Values ℓ -l))
(define (unpack-ℒ ℒ)
  (define ℓ (-ℒ-app ℒ))
  (values ℓ (ℓ-src ℓ)))

(define (ℒ-with-mon [ℒ : -ℒ] [ℓ : ℓ])
  (match-define (-ℒ ℓs ℓₐ) ℒ)
  (-ℒ (set-add ℓs ℓ) ℓₐ))

(define (ℒ-with-l [ℒ : -ℒ] [l : -l])
  (match-define (-ℒ ℓs ℓₐ) ℒ)
  (match-define (loc _ line col id) (ℓ->loc ℓₐ))
  (-ℒ ℓs (loc->ℓ (loc l line col id))))

(struct -edge ([tgt : -⟦e⟧] [src : -ℒ]) #:transparent)
(define-type -ℋ (Listof (U -edge -ℒ)))
(define ℋ∅ : -ℋ '())

(: ℋ+ : -ℋ (U -edge -ℒ)  → -ℋ)
;; Add edge on top of call history.
;; If the target is already there, return the history chunk up to first time the target
;; is seen
(define (ℋ+ ℋ x)
  (define match? : ((U -edge -ℒ) → Boolean)
    (cond [(-ℒ? x) (λ (e) (equal? e x))]
          [(-edge? x)
           (define x.tgt (-edge-tgt x))
           (λ (e) (and (-edge? e) (eq? x.tgt (-edge-tgt e))))]))
  (define ?ℋ (memf match? ℋ))
  (if ?ℋ ?ℋ (cons x ℋ)))


;; The call history is passed around a lot and is part of address allocation
;; So it may be useful to intern for cheaper comparison
(define-interner -ℋ #:interned-type-name -⟪ℋ⟫)
(define ⟪ℋ⟫∅ (-ℋ->-⟪ℋ⟫ ℋ∅))

(: ⟪ℋ⟫+ : -⟪ℋ⟫ (U -edge -ℒ) → -⟪ℋ⟫)
(define (⟪ℋ⟫+ ⟪ℋ⟫ e) (-ℋ->-⟪ℋ⟫ (ℋ+ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫) e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Some address values have `e` embeded in them.
;; This used to be a neccessary precision hack.
;; Nowaways it's just a temporary fix for the inaccurate source location returned
;; by `fake-contract`
(-α . ::= . ; For wrapped top-level definition
            (-α.wrp -𝒾)
            ; for binding
            (-α.x Symbol -⟪ℋ⟫ (℘ -h))
            (-α.fv -⟪ℋ⟫ (℘ -t))
            ; for struct field
            (-α.fld [id : -𝒾] [loc : -ℒ] [ctx : -⟪ℋ⟫] [idx : Natural])
            ; for Cons/varargs
            ; idx prevents infinite list
            (-α.var-car [loc : -ℒ] [ctx : -⟪ℋ⟫] [idx : (Option Natural)])
            (-α.var-cdr [loc : -ℒ] [ctx : -⟪ℋ⟫] [idx : (Option Natural)])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [loc : -ℒ] [ctx : -⟪ℋ⟫] [l+ : -l])

            ;; for vector indices
            (-α.idx [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            
            ;; for vector^ content
            (-α.vct [loc : ℓ] [ctx : -⟪ℋ⟫])

            ;; for wrapped vector
            (-α.unvct [loc : -ℒ] [ctx : -⟪ℋ⟫] [l+ : -l])

            ;; for contract components
            (-α.and/c-l [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.and/c-r [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.or/c-l [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.or/c-r [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.not/c [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.vector/c [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.vectorof [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.struct/c [sym : -?t] [id : -𝒾] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.x/c Symbol)
            (-α.dom [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫] [idx : Natural])
            (-α.rst [sym : -?t] [loc : ℓ] [ctd : -⟪ℋ⟫])
            (-α.rng [sym : -?t] [loc : ℓ] [ctx : -⟪ℋ⟫])
            (-α.fn [sym : -?t] [mon-loc : -ℒ] [ctx : -⟪ℋ⟫] [l+ : -l] [pc : (℘ -t)])

            ;; HACK
            (-α.hv)
            (-α.mon-x/c Symbol -⟪ℋ⟫ -l (℘ -h))
            (-α.fc-x/c Symbol -⟪ℋ⟫ (℘ -h))

            -o
            -𝒾
            (-α.e -e ℓ -⟪ℋ⟫))

(define-interner -α #:interned-type-name ⟪α⟫)
(define ⟪α⟫ₕᵥ (-α->⟪α⟫ (-α.hv)))

(define ⊥σ (-σ (hasheq ⟪α⟫ₕᵥ ∅) ∅eq (hasheq)))
(define (⊥Σ) (-Σ ⊥σ ⊥σₖ ⊥M))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cache for address lookup in local block
;; TODO: merge this in as part of path-condition
(define-type -$ (HashTable -t -V))
(define $∅ : -$ (hash))
(define ($@ [$ : -$] [t : -?t]) : (Option -V)
  (and t (hash-ref $ t #f)))

(define ($+ [$ : -$] [t : -?t] [V : -V]) : -$
  (if t (hash-set $ t V) $))

;; A computation returns set of next states
;; and may perform side effects widening mutable store(s)
(define-type -⟦e⟧ (-ρ -$ -Γ -⟪ℋ⟫ -Σ -⟦k⟧ → (℘ -ς)))
(define-type -⟦k⟧ (-A -$ -Γ -⟪ℋ⟫ -Σ     → (℘ -ς)))
(define-values (remember-e! recall-e) ((inst make-memoeq -⟦e⟧ -e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(-ς . ::= . #|block start |# (-ς↑ -αₖ -Γ -⟪ℋ⟫)
            #|block return|# (-ς↓ -αₖ -Γ -A))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(-αₖ . ::= . (-ℬ [var : -formals] [exp : -⟦e⟧] [env : -ρ])
     ;; Contract monitoring
     (-ℳ [var : Symbol] [l³ : -l³] [loc : -ℒ] [ctc : -V] [val : ⟪α⟫])
     ;; Flat checking
     (-ℱ [var : Symbol] [l : -l] [loc : -ℒ] [ctc : -V] [val : ⟪α⟫])
     ;; Havoc
     (-ℋ𝒱)
     )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Convenient paterns
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-match-expander -Cons
  (syntax-rules () [(_ αₕ αₜ) (-St (== -𝒾-cons) (list αₕ αₜ))])
  (syntax-rules () [(_ αₕ αₜ) (-St -𝒾-cons      (list αₕ αₜ))]))
(define-match-expander -Cons*
  (syntax-rules () [(_ α) (-St* (-St/C _ (== -𝒾-cons) _) α _)]))
(define-match-expander -Box
  (syntax-rules () [(_ α) (-St (== -𝒾-box) (list α))])
  (syntax-rules () [(_ α) (-St -𝒾-box      (list α))]))
(define-match-expander -Box*
  (syntax-rules () [(_ α) (-St* (-St/C _ (== -𝒾-box) _) α _)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-ς [ς : -ς]) : Sexp
  (match ς
    [(-ς↑ αₖ Γ ⟪ℋ⟫) `(ev: ,⟪ℋ⟫ ,(show-αₖ αₖ) ‖ ,@(show-Γ Γ))]
    [(-ς↓ αₖ Γ A)  `(rt: ,(show-αₖ αₖ) ,(show-A A) ‖ ,@(show-Γ Γ))]))

(define (show-Σ [Σ : -Σ]) : (Values (Listof Sexp) (Listof Sexp) (Listof Sexp))
  (match-define (-Σ σ σₖ M) Σ)
  (values (show-σ σ) (show-σₖ σₖ) (show-M M)))

(define (show-σ [σ : (U -σ (HashTable ⟪α⟫ (℘ -V)))]) : (Listof Sexp)
  (cond [(-σ? σ) (show-σ (-σ-m σ))]
        [else
         (for*/list : (Listof Sexp) ([(⟪α⟫ᵢ Vs) σ]
                                     [α (in-value (⟪α⟫->-α (cast #|FIXME TR|# ⟪α⟫ᵢ ⟪α⟫)))])
           `(,(show-⟪α⟫ (cast #|FIXME TR|# ⟪α⟫ᵢ ⟪α⟫)) ↦ ,@(set-map Vs show-V)))]))

(define (show-h [h : -h])
  (match h
    [(? -o?) (show-o h)]
    [(? -αₖ?) (show-αₖ h)]
    [(? -V? V) (show-V V)]
    [(-st/c.mk 𝒾) (format-symbol "~a/c" (-𝒾-name 𝒾))]
    [(-st/c.ac 𝒾 i) (format-symbol "~a/c._~a" (-𝒾-name 𝒾) (n-sub i))]
    [(-->i.mk) '-->i]
    [(-->i.dom i) (format-symbol "-->i._~a" (n-sub i))]
    [(-->i.rng) '-->i.rng]
    [(-->.mk) '-->]
    [(-->*.mk) '-->*]
    [(-->.dom i) (format-symbol "-->._~a" (n-sub i))]
    [(-->.rst) '-->.rest]
    [(-->.rng) '-->.rng]
    [(-ar.mk) 'arr]
    [(-ar.ctc) 'arr.ctc]
    [(-ar.fun) 'arr.fun]
    [(-values.ac i) (format-symbol "values._~a" (n-sub i))]
    [(-≥/c b) `(≥/c ,(show-b b))]
    [(-≤/c b) `(≤/c ,(show-b b))]
    [(->/c b) `(>/c ,(show-b b))]
    [(-</c b) `(</c ,(show-b b))]
    [(-≡/c b) `(≡/c ,(show-b b))]
    [(-≢/c b) `(≢/c ,(show-b b))]
    [(-not/c o) `(not/c ,(show-o o))]))

(define (show-t [?t : -?t]) : Sexp
  (match ?t
    [#f '∅]
    [(? -e? e) (show-e e)]
    [(-t.@ h ts) `(@ ,(show-h h) ,@(map show-t ts))]))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ ts as) Γ)
  `(,@(set-map ts show-t)
    ,@(for/list : (Listof Sexp) ([(x t) (in-hash as)])
        `(,x ↦ ,(show-t t)))))

(define (show-σₖ [σₖ : (U -σₖ (HashTable -αₖ (℘ -κ)))]) : (Listof Sexp)
  (for/list ([(αₖ κs) σₖ])
    `(,(show-αₖ αₖ) ↦ ,@(set-map κs show-κ))))

(define (show-M [M : (U -M (HashTable -αₖ (℘ -ΓA)))]) : (Listof Sexp)
  (for/list ([(αₖ As) M])
    `(,(show-αₖ αₖ) ↦ ,@(set-map As show-ΓA))))

(define show-blm-reason : ((U -V -v -h) → Sexp)
  (match-lambda
    [(? -V? V) (show-V V)]
    [(? -v? v) (show-e v)]
    [(? -h? h) (show-h h)]))

(define (show-V [V : -V]) : Sexp
  (match V
    [(-b b) (show-b b)]
    [(-● ps)
     (string->symbol
      (string-join
       (for/list : (Listof String) ([p ps])
         (format "_~a" (show-h p)))
       ""
       #:before-first "●"))]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧ ρ _) `(λ ,(show-formals xs) ,(show-⟦e⟧ ⟦e⟧))]
    [(-Case-Clo clauses ρ Γ)
     `(case-lambda
       ,@(for/list : (Listof Sexp) ([clause clauses])
           (match-define (cons xs _) clause)
           `(,xs …)))]
    [(-Ar guard α _)
     (match α
       [(? -𝒾? 𝒾) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
       [(-α.wrp 𝒾) (format-symbol "⟪~a⟫" (-𝒾-name 𝒾))]
       [_ `(,(show-V guard) ◃ ,(show-⟪α⟫ α))])]
    [(-St 𝒾 αs) `(,(-𝒾-name 𝒾) ,@(map show-⟪α⟫ αs))]
    [(-St* (-St/C _ 𝒾 γℓs) α _)
     `(,(format-symbol "~a/wrapped" (-𝒾-name 𝒾))
       ,@(for/list : (Listof Sexp) ([γℓ γℓs]) (if γℓ (show-⟪α⟫ℓ γℓ) '✓))
       ▹ ,(show-⟪α⟫ α))]
    [(-Vector αs) `(vector ,@(map show-⟪α⟫ αs))]
    [(-Vector^ α n) `(vector^ ,(show-⟪α⟫ α) ,(show-V n))]
    [(-Vector/guard grd _ _)
     (match grd
       [(-Vector/C γs) `(vector/diff ,@(map show-⟪α⟫ℓ γs))]
       [(-Vectorof γ) `(vector/same ,(show-⟪α⟫ℓ γ))])]
    [(-And/C _ l r) `(and/c ,(show-⟪α⟫ (car l)) ,(show-⟪α⟫ (car r)))]
    [(-Or/C _ l r) `(or/c ,(show-⟪α⟫ (car l)) ,(show-⟪α⟫ (car r)))]
    [(-Not/C γ) `(not/c ,(show-⟪α⟫ (car γ)))]
    [(-One-Of/C vs) `(one-of/c ,@(map show-b vs))]
    [(-Vectorof γ) `(vectorof ,(show-⟪α⟫ (car γ)))]
    [(-Vector/C γs) `(vector/c ,@(map show-⟪α⟫ (map ⟪α⟫ℓ->⟪α⟫ γs)))]
    [(-=> αs β _)
     (match αs
       [(-var αs α) `(,(map show-⟪α⟫ℓ αs) #:rest ,(show-⟪α⟫ℓ α) . ->* . ,(show-⟪α⟫ℓ β))]
       [(? list? αs) `(,@(map show-⟪α⟫ℓ αs) . -> . ,(show-⟪α⟫ℓ β))])]
    [(-=>i γs (list (-Clo _ ⟦e⟧ _ _) (-λ xs d) _) _)
     `(->i ,@(map show-⟪α⟫ℓ γs)
           ,(match xs
              [(? list? xs) `(res ,xs ,(show-e d))]
              [_ (show-e d)]))]
    [(-Case-> cases _)
     `(case->
       ,@(for/list : (Listof Sexp) ([kase cases])
           (match-define (cons αs β) kase)
           `(,@(map show-⟪α⟫ αs) . -> . ,(show-⟪α⟫ β))))]
    [(-St/C _ 𝒾 αs)
     `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(map show-⟪α⟫ (map ⟪α⟫ℓ->⟪α⟫ αs)))]
    [(-x/C ⟪α⟫) `(recursive-contract ,(show-⟪α⟫ ⟪α⟫))]))

(define (show-⟪α⟫ℓ [⟪α⟫ℓ : (Pairof ⟪α⟫ ℓ)]) : Symbol
  (match-define (cons ⟪α⟫ ℓ) ⟪α⟫ℓ)
  (define α (⟪α⟫->-α ⟪α⟫))
  (string->symbol
   (format "~a~a" (if (-e? α) (show-e α) (show-⟪α⟫ ⟪α⟫)) (n-sup ℓ))))

(define (show-ΓA [ΓA : -ΓA]) : Sexp
  (match-define (-ΓA Γ A) ΓA)
  `(,(show-A A) ‖ ,(show-Γ Γ)))

(define (show-A [A : -A])
  (cond [(-W? A) (show-W A)]
        [else (show-blm A)]))

(define (show-W [W : -W]) : Sexp
  (match-define (-W Vs t) W)
  `(,@(map show-V Vs) @ ,(show-t t)))

(define (show-W¹ [W : -W¹]) : Sexp
  (match-define (-W¹ V t) W)
  `(,(show-V V) @ ,(show-t t)))

(define (show-blm [blm : -blm]) : Sexp
  (match-define (-blm l+ lo Cs Vs ℓ) blm)
  (match* (Cs Vs)
    [('() (list (-b (? string? msg)))) `(error ,msg)] ;; HACK
    [(_ _) `(blame ,l+ ,lo ,(map show-blm-reason Cs) ,(map show-V Vs) ,(show-ℓ ℓ))]))

(define show-⟦e⟧ : (-⟦e⟧ → Sexp)
  (let-values ([(⟦e⟧->symbol symbol->⟦e⟧ _) ((inst unique-sym -⟦e⟧) '⟦e⟧)])
    (λ (⟦e⟧)
      (cond [(recall-e ⟦e⟧) => show-e]
            [else (⟦e⟧->symbol ⟦e⟧)]))))

(define (show-αₖ [αₖ : -αₖ]) : Sexp
  (cond [(-ℬ? αₖ) (show-ℬ αₖ)]
        [(-ℳ? αₖ) (show-ℳ αₖ)]
        [(-ℱ? αₖ) (show-ℱ αₖ)]
        [(-ℋ𝒱? αₖ) 'ℋ𝒱]
        [else     (error 'show-αₖ "~a" αₖ)]))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ xs ⟦e⟧ ρ #;_) ℬ)
  (match xs
    ['() `(ℬ ()                 ,(show-⟦e⟧ ⟦e⟧) ,(show-ρ ρ))]
    [_   `(ℬ ,(show-formals xs) …               ,(show-ρ ρ))]))

(define (show-ℳ [ℳ : -ℳ]) : Sexp
  (match-define (-ℳ x l³ ℓ C V) ℳ)
  `(ℳ ,x ,(show-V C) ,(show-⟪α⟫ V)))

(define (show-ℱ [ℱ : -ℱ]) : Sexp
  (match-define (-ℱ x l ℓ C V) ℱ)
  `(ℱ ,x ,(show-V C) ,(show-⟪α⟫ V)))

(define-parameter verbose? : Boolean #f)

(define (show-⟪ℋ⟫ [⟪ℋ⟫ : -⟪ℋ⟫]) : Sexp
  (if (verbose?)
      (show-ℋ (-⟪ℋ⟫->-ℋ ⟪ℋ⟫))
      ⟪ℋ⟫))
(define (show-ℋ [ℋ : -ℋ]) : (Listof Sexp)
  (for/list ([e ℋ])
    (match e
      [(-edge ⟦e⟧ ℒ)
       `(,(show-ℒ ℒ) ↝ ,(show-⟦e⟧ ⟦e⟧))]
      [(? -ℒ? ℒ) (show-ℒ ℒ)])))

(define show-ℒ : (-ℒ → Sexp)
  (let-values ([(ℒ->symbol symbol->ℒ _) ((inst unique-sym -ℒ) 'ℒ)])
    (λ (ℒ)
      (cond [(verbose?)
             (match-define (-ℒ ℓs ℓ) ℒ)
             `(ℒ ,(set->list ℓs) ,ℓ)]
            [else (ℒ->symbol ℒ)]))))

(define (show-⟪α⟫ [⟪α⟫ : ⟪α⟫]) : Sexp

  (define (show-α.x [x : Symbol] [⟪ℋ⟫ : -⟪ℋ⟫] [ps : (℘ -h)])
    (for/fold ([s : Symbol (format-symbol "~a_~a" x (n-sub ⟪ℋ⟫))])
              ([p (in-set ps)])
      (format-symbol "~a_~a" s #|HACK|# (string->symbol (format "~a" (show-h p))))))

  (define α (⟪α⟫->-α ⟪α⟫))
  (match (⟪α⟫->-α ⟪α⟫)
    [(-α.x x ⟪ℋ⟫ ps) (show-α.x x ⟪ℋ⟫ ps)]
    [(-α.hv) 'αₕᵥ]
    [(-α.e e ℓ ⟪ℋ⟫) (show-e e)]
    [(-α.mon-x/c x ⟪ℋ⟫ _ ps) (show-α.x x ⟪ℋ⟫ ps)]
    [(-α.fc-x/c x ⟪ℋ⟫ ps) (show-α.x x ⟪ℋ⟫ ps)]
    [(-α.fv ⟪ℋ⟫ ts) (show-α.x 'dummy ⟪ℋ⟫ ∅)]
    [(or (-α.and/c-l (? -t? t) _ _)
         (-α.and/c-r (? -t? t) _ _)
         (-α.or/c-l (? -t? t) _ _)
         (-α.or/c-r (? -t? t) _ _)
         (-α.not/c (? -t? t) _ _)
         (-α.vector/c (? -t? t) _ _ _)
         (-α.vectorof (? -t? t) _ _)
         (-α.struct/c (? -t? t) _ _ _ _)
         (-α.dom (? -t? t) _ _ _)
         (-α.rst (? -t? t) _ _)
         (-α.rng (? -t? t) _ _)
         (-α.fn (? -t? t) _ _ _ _))
     #:when t
     (show-t t)]
    [(? -e? e) (show-e e)]
    [_ (format-symbol "α~a" (n-sub ⟪α⟫))]))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x ⟪α⟫ₓ) ρ] #:unless (equal? x -x-dummy))
    `(,x ↦ ,(show-⟪α⟫ (cast #|FIXME TR|# ⟪α⟫ₓ ⟪α⟫)))))

(define (show-κ [κ : -κ]) : Sexp
  (match-define (-κ ⟦k⟧ pc ⟪ℋ⟫ ts) κ)
  `(□ ,@(map show-t ts) ‖ ,(set-map pc show-t) @ ,(show-⟪ℋ⟫ ⟪ℋ⟫)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; TMP HACKS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TMP hack for part of root set from stack frames
(splicing-let ([m ((inst make-hasheq -⟦k⟧ (℘ ⟪α⟫)))])
  
  (define (add-⟦k⟧-roots! [⟦k⟧ : -⟦k⟧] [αs : (℘ ⟪α⟫)]) : Void
    (hash-update! m ⟦k⟧ (λ ([αs₀ : (℘ ⟪α⟫)]) (∪ αs₀ αs)) →∅eq))
  
  ;; Return the root set spanned by the stack chunk for current block
  (define (⟦k⟧->roots [⟦k⟧ : -⟦k⟧])
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αs "nothing for ~a" ⟦k⟧)))))

;; TMP hack for mapping stack to stack address to return to
(splicing-let ([m ((inst make-hasheq -⟦k⟧ -αₖ))])

  (define (set-⟦k⟧->αₖ! [⟦k⟧ : -⟦k⟧] [αₖ : -αₖ]) : Void
    (hash-update! m ⟦k⟧
                  (λ ([αₖ₀ : -αₖ]) ; just for debugging
                    (assert (equal? αₖ₀ αₖ))
                    αₖ₀)
                  (λ () αₖ)))
  
  (define (⟦k⟧->αₖ [⟦k⟧ : -⟦k⟧]) : -αₖ
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αₖ "nothing for ~a" ⟦k⟧)))))
