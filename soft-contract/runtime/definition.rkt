#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/string
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt")
(require/typed racket/base
  [(hash-empty? ρ-empty?) (-ρ → Boolean)])
(provide ρ-empty?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Environment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -ρ (HashTable Var-Name -α))
(define-type -Δρ -ρ)
(define ⊥ρ : -ρ (hasheq))
(define (ρ@ [ρ : -ρ] [x : Var-Name]) : -α
  (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
(define ρ+ : (-ρ Var-Name -α → -ρ) hash-set)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Store maps each address to value set and whether it may have been mutated

(struct -σr ([vals : (℘ -V)] [old? : Boolean]) #:transparent)
(struct -σ ([m : (HashTable -α -σr)] [version : Fixnum]) #:transparent #:mutable)
;(define-type -Δσ -σ)
(define (⊥σ) (-σ (hash) 0))
(define ⊥σr (-σr ∅ #t))

(: σ@ : -σ -α → (Values (℘ -V) Boolean))
(define (σ@ σ α)
  (with-debugging/off
    ((Vs old?)
     (match-define (-σr Vs old?) (hash-ref (-σ-m σ) α (λ () (error 'σ@ "no address ~a" α))))
     (values Vs old?))
    (when (>= (set-count Vs) 9)
      (printf "σ@: ~a -> ~a~n" (show-α α) (set-count Vs)))))

(: σ@ᵥ : -σ -α → (℘ -V))
(define (σ@ᵥ σ α)
  (define-values (Vs _) (σ@ σ α))
  Vs)

(: σr⊔ : -σr -V Boolean → -σr)
(define (σr⊔ σr V bind?)
  (match-define (-σr Vs bind?₀) σr)
  (-σr (set-add Vs V) (and bind?₀ bind?)))

(: σ⊔! : -σ -α -V Boolean → Void)
(define (σ⊔! σ α V bind?)
  (match-define (-σ m i) σ)
  (match-define (and σr (-σr Vs b?)) (hash-ref m α (λ () ⊥σr)))
  (unless (and (∋ Vs V) (equal? b? bind?))
    (set--σ-m! σ (hash-update m α (λ ([σr : -σr]) (σr⊔ σr V bind?)) (λ () ⊥σr)))
    (set--σ-version! σ (assert (+ 1 i) fixnum?))))

(define-syntax σ⊔*!
  (syntax-rules (↦)
    [(_ σ [α ↦ V b?]) (σ⊔! σ α V b?)]
    [(_ σ [α ↦ V b?] p ...)
     (begin
       (σ⊔!  σ α V b?)
       (σ⊔*! σ p ...))]))

(: σ-remove! : -σ -α -V → Void)
(define (σ-remove! σ α V)
  (define m*
    (hash-update (-σ-m σ)
                 α
                 (λ ([σr : -σr])
                   (match-define (-σr Vs b?) σr)
                   (-σr (set-remove Vs V) b?))))
  (set--σ-m! σ m*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -κ ([cont : -⟦k⟧!]      ; rest of computation waiting on answer
            [Γ : -Γ]          ; path-condition to use for rest of computation
            [𝒞 : -𝒞]         ; context of rest of computation
            [bnd : (Pairof -s (Listof -s))] ; symbol for result
            )
  #:transparent)

(define-type -σₖ (VMap -αₖ -κ))
(define ⊥σₖ (inst ⊥vm -αₖ -κ))
(define σₖ@ : (-σₖ -αₖ → (℘ -κ)) vm@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Memo Table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type -M (VMap -αₖ -ΓA))
(define ⊥M (inst ⊥vm -αₖ -ΓA))
(define M@ : (-M -αₖ → (℘ -ΓA)) vm@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Grouped reference to mutable stores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -Σ ([σ : -σ] [σₖ : -σₖ] [M : -M]) #:transparent)
(define (⊥Σ) (-Σ (⊥σ) (⊥σₖ) (⊥M)))

(: -Σ-version : -Σ → (Values Fixnum Fixnum Fixnum))
(define -Σ-version
  (match-lambda
    [(-Σ σ σₖ M) (values (-σ-version σ) (VMap-version σₖ) (VMap-version M))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . 'undefined
            -prim
            (-● (℘ -o))
            (-St -struct-info (Listof (U -α.fld -α.var-car -α.var-cdr)))
            (-Vector (Listof -α.idx))
            -Fn
            
            ;; Proxied higher-order values
            (-Ar [guard : #|ok, no rec|# -=>_] [v : -α] [ctx : -l³])
            (-St* [info : -struct-info] [ctcs : (Listof (Option -α))] [val : -α.st] [ctx : -l³])
            (-Vector/hetero [ctcs : (Listof -α)] [ctx : -l³])
            (-Vector/homo [ctc : -α] [ctx : -l³])
            
            -C)

(-Fn . ::= . (-Clo -formals -⟦e⟧! -ρ -Γ)
             (-Case-Clo (Listof (Pairof (Listof Var-Name) -⟦e⟧!)) -ρ -Γ))

;; Contract combinators
(-C . ::= . (-And/C [flat? : Boolean]
                    [l : (Pairof (U -α.and/c-l -α.cnst) -ℓ)]
                    [r : (Pairof (U -α.and/c-r -α.cnst) -ℓ)])
            (-Or/C [flat? : Boolean]
                   [l : (Pairof (U -α.or/c-l -α.cnst) -ℓ)]
                   [r : (Pairof (U -α.or/c-r -α.cnst) -ℓ)])
            (-Not/C (Pairof (U -α.not/c -α.cnst) -ℓ))
            (-x/C [c : (U -α.x/c)])
            ;; Guards for higher-order values
            -=>_
            (-St/C [flat? : Boolean]
                   [info : -struct-info]
                   [fields : (Listof (Pairof (U -α.struct/c -α.cnst) -ℓ))])
            (-Vectorof (Pairof (U -α.vectorof -α.cnst) -ℓ))
            (-Vector/C (Listof (Pairof (U -α.vector/c -α.cnst) -ℓ))))

;; Function contracts
(-=>_ . ::= . (-=>  [doms : (Listof (Pairof (U -α.dom -α.cnst) -ℓ))] [rng : (Pairof -α -ℓ)] [pos : -ℓ])
              (-=>i [doms : (Listof (Pairof (U -α.dom -α.cnst) -ℓ))]
                    [mk-rng : (List -Clo -λ -ℓ)]
                    [pos : -ℓ])
              (-Case-> (Listof (Pairof (Listof -α.dom) -α.rng)) [pos : -ℓ]))

(struct -blm ([violator : -l] [origin : -l]
              [c : (Listof -V)] [v : (Listof -V)]) #:transparent)
(struct -W¹ ([V : -V] [s : -s]) #:transparent)
(struct -W ([Vs : (Listof -V)] [s : -s]) #:transparent)
(-A . ::= . -W -blm)
(struct -ΓA ([cnd : -Γ] [ans : -A]) #:transparent)

(define αℓ->α (inst car -α -ℓ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Path condition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Symbolic value is either pure, refinable expression, or the conservative unrefinable `#f`
(-s . ::= . -e #f)

;; Path condition is set of (pure) expression known to have evaluated to non-#f
;; Tails are addresses to other path-condition "chunks" from function calls,
;; each paired with appropriate renaming.
;; Tails are ordered from least to most recent application.
;; Order is important for effective rewriting. TODO obsolete, no longer need to preserve order
(struct -Γ ([facts : (℘ -e)]
            [aliases : (HashTable Var-Name -e)]
            [tails : (Listof -γ)]) #:transparent)

;; Path condition tail is callee block and renaming information,
;; also indicating whether the call raised a blame or not
(struct -γ ([callee : -αₖ] ; be careful with this. May build up infinitely
            [sym : (Pairof -s (Listof -s))]
            [blm : (Option (Pairof -l -l))]) #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq) '()))

(: Γ+ : -Γ -s * → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ . ss)
  (match-define (-Γ φs as ts) Γ)
  (define φs*
    (for/fold ([φs : (℘ -e) φs]) ([s ss] #:when s)
      (set-add φs s)))
  (-Γ φs* as ts))

(: -Γ-with-aliases : -Γ Var-Name -s → -Γ)
(define (-Γ-with-aliases Γ x s)
  (cond [s (match-define (-Γ φs as ts) Γ)
           (-Γ φs (hash-set as x s) ts)]
        [else Γ]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Call history
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes monitor + call site
(struct -ℒ ([mons : (℘ -ℓ)] [app : -ℓ]) #:transparent)

(define (ℒ-with-mon [ℒ : -ℒ] [ℓ : -ℓ])
  (match-define (-ℒ ℓs ℓₐ) ℒ)
  (-ℒ (set-add ℓs ℓ) ℓₐ))

(define-new-subtype -𝒞 (+𝒞 Natural))
(define-values (𝒞∅ 𝒞+ decode-𝒞)
  (let-values ([(s∅ s+ decode) ((inst make-indexed-set (Pairof -⟦e⟧! -ℒ)))])
    (values (+𝒞 s∅)
            (λ ([𝒞 : -𝒞] [x : (Pairof -⟦e⟧! -ℒ)]) (+𝒞 (s+ 𝒞 x)))
            decode)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value address
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(-α.cnst . ::= . -e)
(-α . ::= . ; For top-level definition and contract
            (-α.def -𝒾)
            (-α.wrp -𝒾)
            ; for binding
            (-α.x Var-Name -𝒞)
            ; for struct field
            (-α.fld [id : -𝒾] [pos : -ℒ] [ctx : -𝒞] [idx : Natural])
            ; for Cons/varargs
            (-α.var-car [pos : -ℓ] [ctx : -𝒞] [idx : Natural]) ; idx prevents infinite list 
            (-α.var-cdr [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

            ;; for wrapped mutable struct
            (-α.st [id : -𝒾] [pos : -ℓ] [ctx : -𝒞])

            ;; for vector indices
            (-α.idx [pos : -ℓ] [ctx : -𝒞] [idx : Natural])

            ;; for contract components
            (-α.and/c-l [pos : -ℓ] [ctx : -𝒞])
            (-α.and/c-r [pos : -ℓ] [ctx : -𝒞])
            (-α.or/c-l [pos : -ℓ] [ctx : -𝒞])
            (-α.or/c-r [pos : -ℓ] [ctx : -𝒞])
            (-α.not/c [pos : -ℓ] [ctx : -𝒞])
            (-α.vector/c [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            (-α.vectorof [pos : -ℓ] [ctx : -𝒞])
            (-α.struct/c [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            (-α.x/c [pos : -ℓ])
            (-α.dom [pos : -ℓ] [ctx : -𝒞] [idx : Natural])
            (-α.rng [pos : -ℓ] [ctx : -𝒞])
            (-α.fn [mon-pos : -ℓ] [guard-pos : -ℓ] [ctx : -𝒞])

            -α.cnst)

(define (α->s [α : -α]) : -s (and (-e? α) α))
(define (αs->ss [αs : (Listof -α)]) : (Listof -s) (map α->s αs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A computation returns set of next states
;; and may perform side effects widening mutable store(s)
(define-type -⟦e⟧! (-ρ -Γ -𝒞 -Σ -⟦k⟧! → (℘ -ς)))
(define-type -⟦k⟧! (-A -Γ -𝒞 -Σ       → (℘ -ς)))
(define-values (remember-e! recall-e) ((inst make-memoeq -⟦e⟧! -e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration
(-ς . ::= . #|block start |# (-ς↑ -αₖ -Γ -𝒞)
            #|block return|# (-ς↓ -αₖ -Γ -A))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack-address / Evaluation "check-point"
(-αₖ . ::= . (-ℬ [var : -formals] [exp : -⟦e⟧!] [env : -ρ])
             ;; Contract monitoring
             (-ℳ [var : Var-Name] [l³ : -l³] [loc : -ℒ] [ctc : -W¹] [val : -W¹]) ; TODO don't need ℒ
            ;; Flat checking
             (-ℱ [var : Var-Name] [l : -l] [loc : -ℒ] [ctc : -W¹] [val : -W¹])) ; TODO don't need ℒ


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-ς [ς : -ς]) : Sexp
  (match ς
    [(-ς↑ αₖ Γ 𝒞) `(ev: ,𝒞 ,(show-αₖ αₖ) ‖ ,@(show-Γ Γ))]
    [(-ς↓ αₖ Γ A) `(rt: ,(show-αₖ αₖ) ,(show-A A) ‖ ,@(show-Γ Γ))]))

(define (show-Σ [Σ : -Σ]) : (Values (Listof Sexp) (Listof Sexp) (Listof Sexp))
  (match-define (-Σ σ σₖ M) Σ)
  (values (show-σ σ) (show-σₖ σₖ) (show-M M)))

(define (show-σ [σ : (U -σ (HashTable -α -σr) (HashTable -α (℘ -V)))]) : (Listof Sexp)
  (cond [(-σ? σ) (show-σ (-σ-m σ))]
        [else
         (for/list ([(α r) σ] #:unless (or (-α.def? α) (-α.wrp? α) (-e? α)))
           (match r
             [(-σr Vs _) `(,(show-α α) ↦ ,@(set-map Vs show-V))]
             [(? set? Vs) `(,(show-α α) ↦ ,@(set-map Vs show-V))]))]))

(define (show-s [s : -s]) (if s (show-e s) '∅))

(define (show-Γ [Γ : -Γ]) : (Listof Sexp)
  (match-define (-Γ φs _ γs) Γ)
  `(,@(set-map φs show-e) ,@(map show-γ γs)))

(define (show-σₖ [σₖ : (U -σₖ (HashTable -αₖ (℘ -κ)))]) : (Listof Sexp)
  (cond [(VMap? σₖ) (show-σₖ (VMap-m σₖ))]
        [else
         (for/list ([(αₖ κs) σₖ])
           `(,(show-αₖ αₖ) ↦ ,@(set-map κs show-κ)))]))

(define (show-M [M : (U -M (HashTable -αₖ (℘ -ΓA)))]) : (Listof Sexp)
  (cond [(VMap? M) (show-M (VMap-m M))]
        [else
         (for/list ([(αₖ As) M])
           `(,(show-αₖ αₖ) ↦ ,@(set-map As show-ΓA)))]))

(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-● ps)
     (string->symbol (string-join (map symbol->string (cons '● (set-map ps show-o))) "_"))]
    [(? -o? o) (show-o o)]
    [(-Clo xs ⟦e⟧! ρ _) `(λ ,(show-formals xs) ,(show-⟦e⟧! ⟦e⟧!))]
    [(-Case-Clo clauses ρ Γ)
     `(case-lambda
       ,@(for/list : (Listof Sexp) ([clause clauses])
           (match-define (cons xs _) clause)
           `(,xs …)))]
    [(-Ar guard α _)
     (match α
       [(-α.def 𝒾) (format-symbol "⟨~a⟩" (-𝒾-name 𝒾))]
       [(-α.wrp 𝒾) (format-symbol "⟪~a⟫" (-𝒾-name 𝒾))]
       [_ `(,(show-V guard) ◃ ,(show-α α))])]
    [(-St s αs) `(,(show-struct-info s) ,@(map show-α αs))]
    [(-St* s γs α _)
     `(,(format-symbol "~a/wrapped" (show-struct-info s))
       ,@(for/list : (Listof Sexp) ([γ γs]) (if γ (show-α γ) '✓))
       ▹ ,(show-α α))]
    [(-Vector αs) `(vector ,@(map show-α αs))]
    [(-Vector/hetero γs _) `(vector/hetero ,@(map show-α γs))]
    [(-Vector/homo γ _) `(vector/homo ,(show-α γ))]
    [(-And/C _ l r) `(and/c ,(show-α (car l)) ,(show-α (car r)))]
    [(-Or/C _ l r) `(or/c ,(show-α (car l)) ,(show-α (car r)))]
    [(-Not/C γ) `(not/c ,(show-α (car γ)))]
    [(-Vectorof γ) `(vectorof ,(show-α (car γ)))]
    [(-Vector/C γs) `(vector/c ,@(map show-α (map αℓ->α γs)))]
    [(-=> αs β _) `(,@(map show-α (map αℓ->α αs)) . -> . ,(show-α (car β)))]
    [(-=>i γs (list (-Clo _ ⟦e⟧ _ _) (-λ xs d) _) _)
     (define cs : (Listof -s)
       (for/list ([γ : (Pairof -α -ℓ) γs])
         (and (-e? (car γ)) (car γ))))
     #;(define d : -s (and (-e? (car α)) (car α)))
     `(->i ,@(map show-s cs)
           ,(match xs
              [(? list? xs) `(res ,xs ,(show-e d))]
              [_ (show-e d)]))]
    [(-Case-> cases _)
     `(case->
       ,@(for/list : (Listof Sexp) ([kase cases])
           (match-define (cons αs β) kase)
           `(,@(map show-α αs) . -> . ,(show-α β))))]
    [(-St/C _ s αs)
     `(,(format-symbol "~a/c" (show-struct-info s)) ,@(map show-α (map αℓ->α αs)))]
    [(-x/C (-α.x/c ℓ)) `(recursive-contract ,(show-x/c ℓ))]))

(define (show-ΓA [ΓA : -ΓA]) : Sexp
  (match-define (-ΓA Γ A) ΓA)
  `(,(show-A A) ‖ ,(show-Γ Γ)))

(define (show-A [A : -A])
  (cond [(-W? A) (show-W A)]
        [else (show-blm A)]))

(define (show-W [W : -W]) : Sexp
  (match-define (-W Vs s) W)
  `(,@(map show-V Vs) @ ,(show-s s)))

(define (show-W¹ [W : -W¹]) : Sexp
  (match-define (-W¹ V s) W)
  `(,(show-V V) @ ,(show-s s)))

(define (show-blm [blm : -blm]) : Sexp
  (match-define (-blm l+ lo Cs Vs) blm)
  (match* (Cs Vs)
    [('() (list (-b (? string? msg)))) `(error ,msg)] ;; HACK
    [(_ _) `(blame ,l+ ,lo ,(map show-V Cs) ,(map show-V Vs))]))

(: show-bnds : (Listof (Pairof Var-Name -s)) → (Listof Sexp))
(define (show-bnds bnds) (map show-bnd bnds))

(define (show-bnd [x-s : (Pairof Var-Name -s)])
  (match-define (cons x s) x-s)
  `(,x ↦ ,(show-s s)))

(define show-⟦e⟧! : (-⟦e⟧! → Sexp)
  (let-values ([(⟦e⟧->symbol symbol->⟦e⟧! _) ((inst unique-sym -⟦e⟧!) '⟦e⟧)])
    (λ (⟦e⟧)
      (cond [(recall-e ⟦e⟧) => show-e]
            [else (⟦e⟧->symbol ⟦e⟧)]))))

(define (show-αₖ [αₖ : -αₖ]) : Sexp
  (cond [(-ℬ? αₖ) (show-ℬ αₖ)]
        [(-ℳ? αₖ) (show-ℳ αₖ)]
        [(-ℱ? αₖ) (show-ℱ αₖ)]
        [else     (error 'show-αₖ "~a" αₖ)]))

(define (show-ℬ [ℬ : -ℬ]) : Sexp
  (match-define (-ℬ xs ⟦e⟧! ρ) ℬ)
  `(ℬ ,(show-formals xs) ,(show-⟦e⟧! ⟦e⟧!) ,(show-ρ ρ)))

(define (show-ℳ [ℳ : -ℳ]) : Sexp
  (match-define (-ℳ x l³ ℓ W-C W-V) ℳ)
  `(ℳ ,(show-W¹ W-C) ,(show-W¹ W-V)))

(define (show-ℱ [ℱ : -ℱ]) : Sexp
  ;(-ℱ [l : -l] [loc : -ℓ] [ctc : -W¹] [val : -W¹])
  (match-define (-ℱ x l ℓ W-C W-V) ℱ)
  `(ℱ ,(show-W¹ W-C) ,(show-W¹ W-V)))

(define-parameter verbose? : Boolean #f)

(define (show-𝒞 [𝒞 : -𝒞]) : Sexp
  (cond [(verbose?)
         (for/list : (Listof Sexp) ([ctx : (Pairof -⟦e⟧! -ℒ) (decode-𝒞 𝒞)])
           (match-define (cons to from) ctx)
           `(,(show-⟦e⟧! to) ↝ ,(show-ℒ from)))]
        [else (format-symbol "𝒞~a" (n-sub 𝒞))]))

(define show-ℒ : (-ℒ → Sexp)
  (let-values ([(ℒ->symbol symbol->ℒ _) ((inst unique-sym -ℒ) 'ℒ)])
    (λ (ℒ)
      (cond [(verbose?)
             (match-define (-ℒ ℓs ℓ) ℒ)
             `(ℒ ,(set->list ℓs) ,ℓ)]
            [else (ℒ->symbol ℒ)]))))

(define-values (show-α show-α⁻¹)
  (let-values ([(α->symbol symbol->α _) ((inst unique-sym -α) 'α)])
    (values
     (ann
      (match-lambda
        ;[(? -e? α) (show-e α)]
        [(-α.x x 𝒞) (format-symbol "~a_~a" (show-Var-Name x) (n-sub 𝒞))]
        [(? -α? α) (α->symbol α)])
      (-α → Symbol))
     symbol->α)))

(define (show-ρ [ρ : -ρ]) : (Listof Sexp)
  (for/list ([(x α) ρ]) `(,(show-Var-Name x) ↦ ,(show-α α))))

(define show-γ : (-γ → Sexp)
  (let-values ([(show-γ show-γ⁻¹ count-γs) ((inst unique-sym -γ) 'γ)])
    (λ (γ)
      (cond [(verbose?)
             (match-define (-γ αₖ (cons sₕ sₓs) blm) γ)
             `(,(show-αₖ αₖ) ‖ (,(show-s sₕ) ,@(map show-s sₓs)) ‖ ,blm)]
            [else (show-γ γ)]))))

(define (show-κ [κ : -κ]) : Sexp
  (match-define (-κ ⟦k⟧ Γ 𝒞 bnd) κ)
  '⟦κ⟧)
