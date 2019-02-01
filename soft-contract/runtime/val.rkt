#lang typed/racket/base

(provide val@)

(require typed/racket/unit
         racket/match
         racket/set
         (only-in racket/list make-list)
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit val@
  (import meta-functions^ static-info^
          prims^
          sto^)
  (export val^)

  (: collapse-W^ : W^ → W)
  (define (collapse-W^ Ws) (set-fold W⊔ (set-first Ws) (set-rest Ws)))
  
  (: collapse-W^-by-arities : W^ → (Immutable-HashTable Index W))
  (define (collapse-W^-by-arities Ws)
    (for/fold ([acc : (Immutable-HashTable Index W) (hasheq)])
              ([Wᵢ (in-set Ws)])
      (define n (length Wᵢ))
      (hash-update acc n
                   (λ ([W₀ : W]) (W⊔ W₀ Wᵢ))
                   (λ () (make-list n ∅))))) 

  (: V/ : S → V → V)
  (define (V/ S)
    (define (α/ [α : α]) (hash-ref S α (λ () α)))
    (define Clo/ : (Clo → Clo)
      (match-lambda [(Clo xs E αs ℓ) (Clo xs E (map/set α/ αs) ℓ)]))
    (define ==>/ : (==> → ==>)
      (match-lambda [(==> cs d ℓ) (==> (var-map α/ cs) (and d (map α/ d)) ℓ)]))
    (define Dom/ : (Dom → Dom)
      (match-lambda [(Dom x c ℓ) (Dom x (if (Clo? c) (Clo/ c) (α/ c)) ℓ)]))
    (define Prox/C/ : (Prox/C → Prox/C)
      (match-lambda
        [(St/C 𝒾 αs ℓ) (St/C 𝒾 (map α/ αs) ℓ)]
        [(Vectof/C α ℓ) (Vectof/C (α/ α) ℓ)]
        [(Vect/C αs ℓ) (Vect/C (map α/ αs) ℓ)]
        [(Hash/C α₁ α₂ ℓ) (Hash/C (α/ α₁) (α/ α₂) ℓ)]
        [(Set/C α ℓ) (Set/C (α/ α) ℓ)]
        [(? ==>? C) (==>/ C)]
        [(==>i dom rng) (==>i (map Dom/ dom) (Dom/ rng))]
        [(∀/C xs E αs) (∀/C xs E (map/set α/ αs))]
        [(Case-=> Cs) (Case-=> (map ==>/ Cs))]))
    (λ (V₀)
      (let go ([V : V V₀])
        (match V
          [(St 𝒾 αs) (St 𝒾 (map α/ αs))]
          [(Vect αs) (Vect (map α/ αs))]
          [(Vect-Of α Vₙ) (Vect-Of (α/ α) (map/set go Vₙ))]
          [(Hash-Of α₁ α₂ im?) (Hash-Of (α/ α₁) (α/ α₂) im?)]
          [(Set-Of α im?) (Set-Of (α/ α) im?)]
          [(Guarded ctx G α) (Guarded ctx (Prox/C/ G) (α/ α))]
          [(Sealed α) (Sealed (α/ α))]
          [(? Clo? clo) (Clo/ clo)]
          [(Case-Clo clos ℓ) (Case-Clo (map Clo/ clos) ℓ)]
          [(And/C α₁ α₂ ℓ) (And/C (α/ α₁) (α/ α₂) ℓ)]
          [(Or/C α₁ α₂ ℓ) (Or/C (α/ α₁) (α/ α₂) ℓ)]
          [(Not/C α ℓ) (Not/C (α/ α) ℓ)]
          [(? Prox/C? C) (Prox/C/ C)]
          [(Seal/C α) (Seal/C (α/ α))]
          [(? α? α) (α/ α)]
          [V V]))))

  (: W⊔ : W W → W)
  (define (W⊔ W₁ W₂) ((inst map V^ V^ V^) ∪ W₁ W₂))

  (define Ctx-with-site : (Ctx ℓ → Ctx)
    (match-lambda** [((Ctx l+ l- ℓ:o _) ℓ) (Ctx l+ l- ℓ:o ℓ)]))

  (define Ctx-flip : (Ctx → Ctx)
    (match-lambda [(Ctx l+ l- lo ℓ) (Ctx l- l+ lo ℓ)]))

  (: C-flat? : V Σ → Boolean)
  ;; Check whether contract is flat, assuming it's already a contract
  (define (C-flat? C Σ)
    (define-set seen : α #:as-mutable-hash? #t)
    (: go-α : α → Boolean)
    (define (go-α α)
      (cond [(seen-has? α) #t]
            [else (seen-add! α)
                  (set-andmap go-V (unpack α Σ))]))
    (: go-V : V → Boolean)
    (define go-V
      (match-lambda
        [(And/C α₁ α₂ _) (and (go-α α₁) (go-α α₂))]
        [(Or/C α₁ α₂ _) (and (go-α α₁) (go-α α₂))]
        [(? Not/C?) #t]
        [(St/C _ αs _) (andmap go-α αs)]
        [(Hash/C αₖ αᵥ _) (and (go-α αₖ) (go-α αᵥ))]
        [(Set/C α _) (go-α α)]
        [(? Fn/C?) #f]
        [(or (? Clo?) (Guarded _ (? Fn/C?) _) (? -prim?) (? Case-Clo?)) #t]
        [(α:dyn (? β:x/c?) _) #t]
        [(? ∀/C?) #f]
        [(? Seal/C?) #f]
        [V (error 'C-flat? "unexpected: ~a" V)]))
    (go-V C))

  (: C^-flat? : V^ Σ → Boolean)
  (define (C^-flat? C^ Σ)
    (for/and : Boolean ([C (in-set C^)]) (C-flat? C Σ)))

  (: arity (case->
            [Clo → (U Natural arity-at-least)]
            [V → (Option Arity)]))
  (define arity
    (match-lambda
      [(Guarded _ (? Fn/C? G) _) (guard-arity G)]
      [(Clo xs _ _ _) (shape xs)]
      [(Case-Clo clos _) (map arity clos)]
      [(? And/C?) 1]
      [(? Or/C?) 1]
      [(? Not/C?) 1]
      [(? St/C?) 1]
      [(? One-Of/C?) 1]
      [(? -st-p?) 1]
      [(? -st-mut?) 2]
      [(-st-mk 𝒾) (count-struct-fields 𝒾)]
      [(? symbol? o) (prim-arity o)]
      [V #:when (not (Clo? V)) #f]))

  (: guard-arity (case->
                  [==> → (U Natural arity-at-least)]
                  [Fn/C → Arity]))
  (define guard-arity
    (match-lambda
      [(==> doms _ _) (shape doms)]
      [(==>i doms _) (length doms)]
      [(Case-=> cases) (map guard-arity cases)]
      [(∀/C _ E _)
       ;; TODO: real Racket just returns `(arity-at-least 0)`
       (cond [(E-arity E) => values] [else (error 'guard-arity "~a" E)])]))

  (: E-arity (case->
              [--> → (U Natural arity-at-least)]
              [E → Arity]))
  (define E-arity
    (match-lambda
      [(--> doms _ _) (shape doms)]
      [(-->i doms _) (length doms)]
      [(case--> cases) (map E-arity cases)]
      [(-∀/c _ E) (E-arity E)]
      [E (error 'E-arity "~a" E)]))

  (: collect-behavioral-values : W^ Σ → V^)
  (define (collect-behavioral-values Ws Σ)
    (for*/fold ([acc : V^ ∅])
               ([W (in-set Ws)]
                [Vs (in-list W)]
                [V (in-set Vs)] #:when (behavioral? V Σ))
      (set-add acc V)))

  (: behavioral? : V Σ → Boolean)
  ;; Check if value maybe behavioral.
  ;; `#t` is a conservative answer "maybe yes"
  ;; `#f` is a strong answer "definitely no"
  (define (behavioral? V₀ Σ)
    (define-set seen : α #:as-mutable-hash? #t)

    (: check-α : α → Boolean)
    (define (check-α α)
      (cond [(seen-has? α) #f]
            [else (seen-add! α)
                  (set-ormap check (unpack α Σ))]))

    (: check : V → Boolean)
    (define check
      (match-lambda
        [(St _ αs) (ormap check-α αs)]
        [(Vect αs) (ormap check-α αs)]
        [(Vect-Of α _) (check-α α)]
        [(Hash-Of αₖ αᵥ im?) (or (not im?) (check-α αₖ) (check-α αᵥ))]
        [(Set-Of α im?) (or (not im?) (check-α α))]
        [(Guarded _ G α) (or (Fn/C? G) (check-α α))]
        [(==> (-var doms domᵣ) rngs _)
         (or (and (pair? rngs) (ormap check-α rngs))
             (and domᵣ (check-α domᵣ))
             (and rngs (ormap check-α doms)))]
        [(? ==>i?) #t]
        [(Case-=> cases) (ormap check cases)]
        [(or (? Clo?) (? Case-Clo?)) #t]
        [(and T (or (? T:@?) (? α?))) (set-ormap check (unpack T Σ))]
        [_ #f]))

    (check V₀))

  (:* with-negative-party with-positive-party : -l V → V)
  (define with-negative-party
    (match-lambda**
     [(l- (Guarded (Ctx l+ _ ℓₒ ℓ) C α)) (Guarded (Ctx l+ l- ℓₒ ℓ) C α)]
     [(_ V) V]))
  (define with-positive-party
    (match-lambda**
     [(l+ (Guarded (Ctx _ l- ℓₒ ℓ) C α)) (Guarded (Ctx l+ l- ℓₒ ℓ) C α)]
     [(_ V) V]))

  #| 
  (: estimate-list-lengths : (U Σ Σᵥ) V → (℘ (U #f Arity)))
  ;; Estimate possible list lengths from the object language's abstract list
  (define (estimate-list-lengths Σ V)
    ???
    #|
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (define maybe-non-proper-list? : Boolean #f)

    (: arity-inc : Arity → Arity)
    (define arity-inc
      (match-lambda
        [(? exact-integer? n) (+ 1 n)]
        [(arity-at-least n) (arity-at-least (+ 1 n))]))
    
    (: go! : -V → (℘ Arity))
    (define go!
      (match-lambda
        [(-Cons _ αₜ)
         (cond [(seen-has? αₜ) {set (arity-at-least 0)}]
               [else (seen-add! αₜ)
                     (for/union : (℘ Arity) ([V* (in-set (σ@ σ δσ αₜ))])
                       (map/set arity-inc (go! V*)))])]
        [(-b '()) {set 0}]
        [(-● ps) #:when (∋ ps 'list?) {set (arity-at-least 0)}]
        [_ (set! maybe-non-proper-list? #t)
           ∅]))
    (define res
      (match (normalize-arity (set->list (go! V)))
        [(? list? l) (list->set l)]
        [a {set a}]))
      (if maybe-non-proper-list? (set-add res #f) res)
    |#)

  (define cmp-sets : (?Cmp (℘ Any))
    (λ (s₁ s₂)
      (define s₁⊆s₂ (s₁ . ⊆ . s₂))
      (define s₂⊆s₁ (s₂ . ⊆ . s₁))
      (or (and s₁⊆s₂ s₂⊆s₁ '=)
          (and s₁⊆s₂ '<)
          (and s₂⊆s₁ '>))))

  (: set-lift-cmp (∀ (X) (?Cmp X) → (?Cmp (℘ X))))
  (define ((set-lift-cmp cmp*) xs ys)
    (define cache : (Mutable-HashTable X (Mutable-HashTable X ?Ord)) (make-hasheq))
    (for ([x (in-set xs)])
      (define x:cmp : (Mutable-HashTable X ?Ord) (make-hasheq))
      (hash-set! cache x x:cmp)
      (for ([y (in-set ys)])
        (hash-set! x:cmp y (cmp* x y))))
    (define (flip [o : ?Ord]) : ?Ord
      (case o [(>) '<] [(<) '>] [else o]))
    (define (cmp [x : X] [y : X]) : ?Ord
      (match (hash-ref cache x #f)
        [(? values x:cmp) (hash-ref x:cmp y (λ () (flip (cmp y x))))]
        [#f (flip (cmp y x))]))
    (define (⊑ [s₁ : (℘ X)] [s₂ : (℘ X)])
      (for/and : Boolean ([x (in-set s₁)])
        (for/or : Boolean ([y (in-set s₂)])
          (case (cmp x y)
            [(< =) #t]
            [else  #f]))))
    (define xs⊑ys (xs . ⊑ . ys))
    (define ys⊑ys (ys . ⊑ . xs))
    (or (and xs⊑ys ys⊑ys '=)
        (and xs⊑ys '<)
        (and ys⊑ys '>)))

  (: fold-cmp (∀ (X) (?Cmp X) (Listof X) (Listof X) → ?Ord))
  (define (fold-cmp cmp xs ys)
    (let go ([xs : (Listof X) xs] [ys : (Listof X) ys])
      (match* (xs ys)
        [((cons x xs*) (cons y ys*))
         (define x-vs-y (cmp x y))
         (and x-vs-y (concat-ord x-vs-y (go xs* ys*)))]
        [('() '()) '=]
        [(_ _) #f])))

  (: join-by-max (∀ (X) (?Cmp X) → (?Joiner X)))
  (define ((join-by-max cmp) x₁ x₂)
    (case (cmp x₁ x₂)
      [(> =) x₁]
      [(<  ) x₂]
      [else  #f]))

  (: compact-with (∀ (X) (?Joiner X) → (℘ X) X → (℘ X)))
  (define ((compact-with ?⊔) xs x)
    (define-values (subsumed x*)
      (for*/fold ([subsumed : (℘ X) ∅] [x* : X x])
                 ([x₀ (in-set xs)]
                  [?x₁ (in-value (?⊔ x₀ x*))] #:when ?x₁)
        (values (set-add subsumed x₀) ?x₁)))
    (set-add (set-subtract xs subsumed) x*))

  (: iter-⊔ (∀ (X) ((℘ X) X → (℘ X)) → (℘ X) (℘ X) → (℘ X)))
  (define ((iter-⊔ f) xs₁ xs₂)
    (for/fold ([acc : (℘ X) xs₁]) ([x (in-set xs₂)])
      (f acc x)))

  (define Ctx-with-origin : (Ctx ℓ → Ctx)
    (match-lambda**
     [((Ctx l+ l- _ ℓ) ℓ:o) (Ctx l+ l- ℓ:o ℓ)]))

  (define X/C->binder : (X/C → Symbol)
    (match-lambda [(X/C α)
                   (match (inspect-α α)
                     ;; TODO other cases
                     [(-α:x/c x _) x]
                     [(-α:imm:listof x _ _) x])]))
  |#
  )
