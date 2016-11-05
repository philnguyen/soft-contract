#lang typed/racket/base

(provide (all-defined-out))

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

(define-type -ρ (HashTable Var-Name -α.x))
(define-type -Δρ -ρ)
(define ⊥ρ : -ρ (hasheq))
(define (ρ@ [ρ : -ρ] [x : Var-Name]) : -α.x
  (hash-ref ρ x (λ () (error 'ρ@ "~a not in environment ~a" x (hash-keys ρ)))))
(define ρ+ : (-ρ Var-Name -α.x → -ρ) hash-set)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Value Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Store maps each address to value set and whether it may have been mutated

(define-type -cardinality (U 0 1 'N))
(struct -σ ([m : (HashTable -α (℘ -V))]
            [modified : (℘ -α)] ; set of addresses potentially have been mutated
            [cardinality : (HashTable -α -cardinality)]
            )
  #:transparent #:mutable)
(define (⊥σ) (-σ (hash) ∅ (hash)))

(: cardinality+ : -cardinality → -cardinality)
(define (cardinality+ c)
  (case c
    [(0) 1]
    [(1) 'N]
    [else 'N]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Stack Store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct -κ ([cont : -⟦k⟧!]    ; rest of computation waiting on answer
            [Γ : -Γ]         ; path-condition to use for rest of computation
            [𝒞 : -𝒞]        ; context of rest of computation
            [fun : -s]
            [args : (Listof -s)]
            )
  #:transparent)

(define-type -σₖ (VMap -αₖ -κ))
(: ⊥σₖ ([] [(Option -αₖ)] . ->* . -σₖ))
(define (⊥σₖ [αₖ #f])
  (cond
    [αₖ ((inst ⊥vm -αₖ -κ) #:init (list αₖ))]
    [else ((inst ⊥vm -αₖ -κ))]))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-V . ::= . 'undefined
            -prim
            (-● (℘ #|closed|# -v))
            (-St -𝒾 (Listof (U -α.fld -α.var-car -α.var-cdr)))
            (-Vector (Listof -α.idx))
            -Fn
            
            ;; Proxied higher-order values
            (-Ar [guard : #|ok, no rec|# -=>_] [v : -α] [ctx : -l³])
            (-St* [id : -𝒾] [ctcs : (Listof (Option -α))] [val : -α.st] [ctx : -l³])
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
                   [id : -𝒾]
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
            [blm : (Option (Pairof -l -l))]
            [fun : -s]
            [args : (Listof -s)]) #:transparent)

(define ⊤Γ (-Γ ∅ (hasheq) '()))

(: Γ+ : -Γ -s * → -Γ)
;; Strengthen path condition `Γ` with `s`
(define (Γ+ Γ . ss)
  (match-define (-Γ φs as ts) Γ)
  (define φs*
    (for/fold ([φs : (℘ -e) φs]) ([s ss] #:when s #:unless (equal? s -tt))
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
            (-α.var-car [pos : -ℒ] [ctx : -𝒞]) ; idx prevents infinite list 
            (-α.var-cdr [pos : -ℒ] [ctx : -𝒞])

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
            (-α.fn [mon-pos : -ℒ] [guard-pos : -ℓ] [ctx : -𝒞])

            -α.cnst)

(define (α->s [α : -α]) : -s (and (-e? α) α))
(define (αs->ss [αs : (Listof -α)]) : (Listof -s) (map α->s αs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compiled expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cache for address lookup in local block
(define-type -$ (HashTable -e -V))
(define $∅ : -$ (hash))
(define ($@ [$ : -$] [s : -s]) : (Option -V)
  (and s (hash-ref $ s #f)))

(define ($+ [$ : -$] [s : -s] [V : -V]) : -$
  (if s (hash-set $ s V) $))

;; A computation returns set of next states
;; and may perform side effects widening mutable store(s)
(define-type -⟦e⟧! (-ρ -$ -Γ -𝒞 -Σ -⟦k⟧! → (℘ -ς)))
(define-type -⟦k⟧! (-A -$ -Γ -𝒞 -Σ       → (℘ -ς)))
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

(define (show-σ [σ : (U -σ (HashTable -α (℘ -V)))]) : (Listof Sexp)
  (cond [(-σ? σ) (show-σ (-σ-m σ))]
        [else
         (for/list ([(α Vs) σ] #:unless (or (-α.def? α) (-α.wrp? α) (-e? α)))
           `(,(show-α α) ↦ ,@(set-map Vs show-V)))]))

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
     (string->symbol
      (string-join
       (for/list : (Listof String) ([p ps])
         (format "_~a" (show-e p)))
       ""
       #:before-first "●"))]
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
    [(-St 𝒾 αs) `(,(-𝒾-name 𝒾) ,@(map show-α αs))]
    [(-St* 𝒾 γs α _)
     `(,(format-symbol "~a/wrapped" (-𝒾-name 𝒾))
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
    [(-=> αs β _) `(,@(map show-αℓ αs) . -> . ,(show-α (car β)))]
    [(-=>i γs (list (-Clo _ ⟦e⟧ _ _) (-λ xs d) _) _)
     `(->i ,@(map show-αℓ γs)
           ,(match xs
              [(? list? xs) `(res ,xs ,(show-e d))]
              [_ (show-e d)]))]
    [(-Case-> cases _)
     `(case->
       ,@(for/list : (Listof Sexp) ([kase cases])
           (match-define (cons αs β) kase)
           `(,@(map show-α αs) . -> . ,(show-α β))))]
    [(-St/C _ 𝒾 αs)
     `(,(format-symbol "~a/c" (-𝒾-name 𝒾)) ,@(map show-α (map αℓ->α αs)))]
    [(-x/C (-α.x/c ℓ)) `(recursive-contract ,(show-x/c ℓ))]))

(define (show-αℓ [αℓ : (Pairof -α -ℓ)]) : Symbol
  (match-define (cons α ℓ) αℓ)
  (string->symbol
   (format "~a~a" (if (-e? α) (show-e α) (show-α α)) (n-sup ℓ))))

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
  `(ℳ ,(show-Var-Name x) ,(show-W¹ W-C) ,(show-W¹ W-V)))

(define (show-ℱ [ℱ : -ℱ]) : Sexp
  (match-define (-ℱ x l ℓ W-C W-V) ℱ)
  `(ℱ ,(show-Var-Name x) ,(show-W¹ W-C) ,(show-W¹ W-V)))

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
             (match-define (-γ αₖ blm sₕ sₓs) γ)
             `(,(show-αₖ αₖ) ‖ (,(show-s sₕ) ,@(map show-s sₓs)) ‖ ,blm)]
            [else (show-γ γ)]))))

(define (show-κ [κ : -κ]) : Sexp
  (match-define (-κ ⟦k⟧ Γ 𝒞 sₕ sₓs) κ)
  `(,(show-s sₕ) ,@(map show-s sₓs) ‖ ,(show-Γ Γ) @ ,(show-𝒞 𝒞)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; TMP HACKS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TMP hack for part of root set from stack frames
(splicing-let ([m ((inst make-hasheq -⟦k⟧! (℘ -α)))])
  
  (define (add-⟦k⟧-roots [⟦k⟧ : -⟦k⟧!] [αs : (℘ -α)]) : Void
    (hash-update! m ⟦k⟧ (λ ([αs₀ : (℘ -α)]) (∪ αs₀ αs)) →∅))
  
  ;; Return the root set spanned by the stack chunk for current block
  (define (⟦k⟧->roots [⟦k⟧ : -⟦k⟧!])
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αs "nothing for ~a" ⟦k⟧)))))

;; TMP hack for mapping stack to stack address to return to
(splicing-let ([m ((inst make-hasheq -⟦k⟧! -αₖ))])

  (define (set-⟦k⟧->αₖ! [⟦k⟧ : -⟦k⟧!] [αₖ : -αₖ]) : Void
    (hash-update! m ⟦k⟧
                  (λ ([αₖ₀ : -αₖ]) ; just for debugging
                    (assert (equal? αₖ₀ αₖ))
                    αₖ₀)
                  (λ () αₖ)))
  
  (define (⟦k⟧->αₖ [⟦k⟧ : -⟦k⟧!]) : -αₖ
    (hash-ref m ⟦k⟧ (λ () (error '⟦k⟧->αₖ "nothing for ~a" ⟦k⟧)))))
