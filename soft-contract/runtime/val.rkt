#lang typed/racket/base

(provide val@)

(require typed/racket/unit
         racket/match
         racket/set
         (only-in racket/list make-list split-at)
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit val@
  (import meta-functions^ static-info^
          prims^
          sto^ pretty-print^ prover^)
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

  (: W⊔ : W W → W)
  (define (W⊔ W₁ W₂) (map V⊔ W₁ W₂))

  (define Ctx-with-site : (Ctx ℓ → Ctx)
    (match-lambda** [((Ctx l+ l- ℓₒ _) ℓ) (Ctx l+ l- ℓₒ ℓ)]))

  (define Ctx-with-origin : (Ctx ℓ → Ctx)
    (match-lambda** [((Ctx l+ l- _ ℓ) ℓₒ) (Ctx l+ l- ℓₒ ℓ)]))

  (define Ctx-flip : (Ctx → Ctx)
    (match-lambda [(Ctx l+ l- lo ℓ) (Ctx l- l+ lo ℓ)]))

  (: C-flat? : V Σ → Boolean)
  ;; Check whether contract is flat, assuming it's already a contract
  (define (C-flat? C Σ)
    (define-set seen : α #:mutable? #t)
    (: go-α : α → Boolean)
    (define (go-α α)
      (cond [(seen-has? α) #t]
            [else (seen-add! α)
                  (S-andmap go-V^ go-α (Σ@/raw α Σ))]))

    (: go-V^ : V^ → Boolean)
    (define (go-V^ [Vs : V^]) (set-andmap go-V Vs))
    (: go-V : V → Boolean)
    (define go-V
      (match-lambda
        [(And/C α₁ α₂ _) (and (go-α α₁) (go-α α₂))]
        [(Or/C α₁ α₂ _) (and (go-α α₁) (go-α α₂))]
        [(? Not/C?) #t]
        [(? One-Of/C?) #t]
        [(St/C α) (go-α α)]
        [(or (? Vectof/C?) (? Vect/C?)) #f]
        [(Hash/C αₖ αᵥ _) (and (go-α αₖ) (go-α αᵥ))]
        [(Set/C α _) (go-α α)]
        [(? Fn/C?) #f]
        [(or (? Clo?) (Guarded _ (? Fn/C?) _) (? -prim?) (? Case-Clo?)) #t]
        [(X/C α) (go-α α)]
        [(? ∀/C?) #f]
        [(? Seal/C?) #f]
        [(? P?) #t]
        [(? α? α) (go-α α)]
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
      [(-λ xs _ _) (shape xs)]
      [(Clo xs _ _) (shape xs)]
      [(Case-Clo clos _) (map arity clos)]
      [(? And/C?) 1]
      [(? Or/C?) 1]
      [(? Not/C?) 1]
      [(? St/C?) 1]
      [(? One-Of/C?) 1]
      [(? -st-p?) 1]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(-st-mk 𝒾) (count-struct-fields 𝒾)]
      [(? symbol? o) (prim-arity o)]
      [V #:when (not (Clo? V)) #f]))

  (: guard-arity (case->
                  [==>i → (U Natural arity-at-least)]
                  [Fn/C → Arity]))
  (define guard-arity
    (match-lambda
      [(==>i doms _ _) (shape doms)]
      [(Case-=> cases) (map guard-arity cases)]
      [(∀/C _ E _)
       ;; TODO: real Racket just returns `(arity-at-least 0)`
       (cond [(E-arity E) => values] [else (error 'guard-arity "~a" E)])]))

  (: E-arity (case->
              [-->i → (U Natural arity-at-least)]
              [E → Arity]))
  (define E-arity
    (match-lambda
      [(-->i doms _ _) (shape doms)]
      [(case--> cases) (map E-arity cases)]
      [(-∀/c _ E _) (E-arity E)]
      [E (error 'E-arity "~a" E)]))

  (:* with-negative-party with-positive-party : -l V → V)
  (define with-negative-party
    (match-lambda**
     [(l- (Guarded (cons l+ 'dummy-) C α)) (Guarded (cons l+ l-) C α)]
     [(_ V) V]))
  (define with-positive-party
    (match-lambda**
     [(l+ (Guarded (cons 'dummy+ l-) C α)) (Guarded (cons l+ l-) C α)]
     [(_ V) V]))

  (: T-refers-to? : T (℘ Symbol) → Boolean)
  (define (T-refers-to? T₀ xs)
    (let go : Boolean ([T : (U -b T) T₀])
      (match T
        [(γ:lex x) (∋ xs x)]
        [(T:@ _ Ts) (ormap go Ts)]
        [_ #f])))

  (define T:@/simp : (K (Listof (U T -b)) → T)
    (match-lambda**
     [((-st-ac 𝒾 i) (list (T:@ (-st-mk 𝒾) Ts))) (assert (list-ref Ts i) T?)]
     [(K Ts) (T:@ K Ts)]))

  ;; Check if the pair `T S*` encodes a proposition
  ;; This is a temporary HACK that should eventually be obsolete by refactoring
  (define prop? : (T S* → Boolean)
    (match-lambda**
     [((T:@ (or (? K:≡?) (? K:≤?) (? K:=?) (? γ:top?)) _) {singleton-set (? -b?)}) #t]
     [(_ _) #f]))

  (: ac-Ps : -st-ac (℘ P) → (℘ P))
  (define (ac-Ps ac Ps)
    (for/fold ([Ps* : (℘ P) ∅]) ([P (in-set Ps)])
      (match P
        [(P:St (== ac) P*) (set-add Ps* P*)]
        ;; Special case for rest of `list?`. TODO: reduce hack
        ['list? #:when (equal? ac -cdr) (set-add Ps* 'list?)]
        [_ Ps*])))

  (: V⊔ : V^ V^ → V^)
  (define (V⊔ Vs₁ Vs₂)
    (if (> (set-count Vs₁) (set-count Vs₂))
        (set-fold V⊔₁ Vs₁ Vs₂)
        (set-fold V⊔₁ Vs₂ Vs₁)))

  (: V⊔₁ : V V^ → V^)
  (define (V⊔₁ V Vs) (merge/compact₁ V⊕ V Vs))

  (define V⊕ : (V V → (Option V))
    (match-lambda**
     [((? -b? b) (and V (-● Qs))) (and (b∈Ps? b Qs) V)]
     [((and V (-● Qs)) (? -b? b)) (and (b∈Ps? b Qs) V)]
     [((and V₁ (-● Ps)) (and V₂ (-● Qs)))
      (cond [(Ps⇒Ps? Ps Qs) V₂]
            [(Ps⇒Ps? Qs Ps) V₁]
            [(and (= 1 (set-count Ps))
                  (= 1 (set-count Qs))
                  (opposite? (set-first Ps) (set-first Qs)))
             (-● ∅)]
            [else (define Ps* (∩ Ps Qs))
                  (and (set-ormap -o? Ps*) (-● Ps*))])]
     [(V₁ V₂) (and (equal? V₁ V₂) V₁)]))

  (define opposite? : (P P → Boolean)
    (match-lambda**
     [((P:¬ Q) Q) #t]
     [(Q (P:¬ Q)) #t]
     [('values 'not) #t]
     [('not 'values) #t]
     [(_ _) #f]))

  (: b∈Ps? : -b (℘ P) → Boolean)
  (define (b∈Ps? b Ps)
    (define b^ {set b})
    (for/and : Boolean ([P (in-set Ps)])
      (and (meaningful-without-store? P) (eq? '✓ (sat ⊥Σ P b^)))))

  (: Ps⇒Ps? : (℘ P) (℘ P) → Boolean)
  (define (Ps⇒Ps? Ps Qs)
    (for/and : Boolean ([Q (in-set Qs)])
      (for/or : Boolean ([P (in-set Ps)])
        (P⊢P-without-store? P Q))))

  (: P⊢P-without-store? : P P → Boolean)
  (define (P⊢P-without-store? P Q)
    (or (equal? P Q)
        ;; FIXME: ugly redundancy, but `(P:> T)` need store in general
        (and (memq Q '(real? number?))
             (or (P:>? P) (P:≥? P) (P:<? P) (P:≤? P) (P:=? P)))
        (and (meaningful-without-store? P)
             (meaningful-without-store? Q)
             (eq? '✓ (P⊢P ⊥Σ P Q)))))

  (define meaningful-without-store? : (P → Boolean)
    (match-lambda
      [(P:¬ Q) (meaningful-without-store? Q)]
      [(P:St acs Q) (meaningful-without-store? Q)]
      [(or (P:> T) (P:≥ T) (P:< T) (P:≤ T) (P:= T) (P:≡ T)) (-b? T)]
      [(or (? P:arity-includes?) (? -o?)) #t]))

  (: merge/compact (∀ (X) (X X → (Option (Listof X))) X (℘ X) → (℘ X)))
  ;; "Merge" `x` into `xs`, compacting the set according to `⊕`
  (define (merge/compact ⊕ x xs)
    (let loop ([x : X x] [xs : (℘ X) xs])
      (or (for/or : (Option (℘ X)) ([xᵢ (in-set xs)])
            (cond [(equal? x xᵢ) xs]
                  [else (define xs* (⊕ xᵢ x))
                        (and xs* (foldl loop (set-remove xs xᵢ) xs*))]))
          (set-add xs x))))

  (: merge/compact₁ (∀ (X) (X X → (Option X)) X (℘ X) → (℘ X)))
  ;; "Merge" `x` into `xs`, compacting the set according to `⊕`
  (define (merge/compact₁ ⊕ x xs)
    (let loop ([x : X x] [xs : (℘ X) xs])
      (or (for/or : (Option (℘ X)) ([xᵢ (in-set xs)])
            (cond [(equal? x xᵢ) xs]
                  [else (define x* (⊕ xᵢ x))
                        (and x* (loop x* (set-remove xs xᵢ)))]))
          (set-add xs x))))

  (define Vect/C-fields : (Vect/C → (Values α ℓ Index))
    (match-lambda
      [(Vect/C α)
       (match α
         [(α:dyn (β:vect/c-elems ℓ n) _) (values α ℓ n)]
         [(γ:imm:blob S ℓ) (values α ℓ (vector-length S))])]))

  (define St/C-fields : (St/C → (Values α ℓ -𝒾))
    (match-lambda
      [(St/C α)
       (match α
         [(α:dyn (β:st/c-elems ℓ 𝒾) _) (values α ℓ 𝒾)]
         [(γ:imm:blob:st _ ℓ 𝒾) (values α ℓ 𝒾)])]))

  (define St/C-tag : (St/C → -𝒾)
    (match-lambda
      [(St/C α)
       (match α
         [(α:dyn (β:st/c-elems _ 𝒾) _) 𝒾]
         [(γ:imm:blob:st _ _ 𝒾) 𝒾])]))
  )
