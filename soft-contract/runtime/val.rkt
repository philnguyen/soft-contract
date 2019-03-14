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

  (: V/ : S → V → V)
  (define (V/ S)
    (define (α/ [α : α]) (hash-ref S α (λ () α)))
    (define Clo/ : (Clo → Clo)
      (match-lambda [(Clo xs E αs ℓ) (Clo xs E (map/set α/ αs) ℓ)]))
    (define ==>i/ : (==>i → ==>i)
      (match-lambda [(==>i dom rng) (==>i (var-map Dom/ dom) (and rng (map Dom/ rng)))]))
    (define Dom/ : (Dom → Dom)
      (match-lambda [(Dom x c ℓ) (Dom x (if (Clo? c) (Clo/ c) (α/ c)) ℓ)]))
    (define Prox/C/ : (Prox/C → Prox/C)
      (match-lambda
        [(St/C 𝒾 αs ℓ) (St/C 𝒾 (map α/ αs) ℓ)]
        [(Vectof/C α ℓ) (Vectof/C (α/ α) ℓ)]
        [(Vect/C αs ℓ) (Vect/C (map α/ αs) ℓ)]
        [(Hash/C α₁ α₂ ℓ) (Hash/C (α/ α₁) (α/ α₂) ℓ)]
        [(Set/C α ℓ) (Set/C (α/ α) ℓ)]
        [(? ==>i? V) (==>i/ V)]
        [(∀/C xs E αs ℓ) (∀/C xs E (map/set α/ αs) ℓ)]
        [(Case-=> Cs) (Case-=> (map ==>i/ Cs))]))
    (define P/ : (P → P)
      (match-lambda
        [(P:¬ Q) (P:¬ (Q/ Q))]
        [(P:St acs P) (P:St acs (P/ P))]))
    (define Q/ : (Q → Q)
      (match-lambda
        [(P:> T) (P:> (T/ T))]
        [(P:≥ T) (P:≥ (T/ T))]
        [(P:< T) (P:< (T/ T))]
        [(P:≤ T) (P:≤ (T/ T))]
        [(P:= T) (P:= (T/ T))]
        [P P]))
    (define T/ : ((U T -b) → (U T -b))
      (match-lambda
        [(T:@ o Ts) (T:@ o (map T/ Ts))]
        [(? α? α) (α/ α)]
        [(? -b? b) b]))
    (λ (V₀)
      (let go ([V : V V₀])
        (match V
          [(? P? P) (P/ P)]
          [(? T? T) (T/ T)]
          [(St 𝒾 αs Ps) (St 𝒾 (map α/ αs) (map/set P/ Ps))]
          [(Vect αs) (Vect (map α/ αs))]
          [(Vect-Of α Vₙ) (Vect-Of (α/ α) (map/set go Vₙ))]
          [(Hash-Of α₁ α₂) (Hash-Of (α/ α₁) (α/ α₂))]
          [(Set-Of α) (Set-Of (α/ α))]
          [(Guarded ctx G α) (Guarded ctx (Prox/C/ G) (α/ α))]
          [(Sealed α) (Sealed (α/ α))]
          [(? Clo? clo) (Clo/ clo)]
          [(Case-Clo clos ℓ) (Case-Clo (map Clo/ clos) ℓ)]
          [(And/C α₁ α₂ ℓ) (And/C (α/ α₁) (α/ α₂) ℓ)]
          [(Or/C α₁ α₂ ℓ) (Or/C (α/ α₁) (α/ α₂) ℓ)]
          [(Not/C α ℓ) (Not/C (α/ α) ℓ)]
          [(? Prox/C? C) (Prox/C/ C)]
          [(Seal/C α l) (Seal/C (α/ α) l)]
          [(-● Ps) (-● (map/set P/ Ps))]
          [V V]))))

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
                  (set-andmap go-V (Σ@ α Σ))]))
    (: go-V : V → Boolean)
    (define go-V
      (match-lambda
        [(And/C α₁ α₂ _) (and (go-α α₁) (go-α α₂))]
        [(Or/C α₁ α₂ _) (and (go-α α₁) (go-α α₂))]
        [(? Not/C?) #t]
        [(? One-Of/C?) #t]
        [(St/C _ αs _) (andmap go-α αs)]
        [(Hash/C αₖ αᵥ _) (and (go-α αₖ) (go-α αᵥ))]
        [(Set/C α _) (go-α α)]
        [(? Fn/C?) #f]
        [(or (? Clo?) (Guarded _ (? Fn/C?) _) (? -prim?) (? Case-Clo?)) #t]
        [(X/C α) (go-α α)]
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
      [(==>i doms _) (shape doms)]
      [(Case-=> cases) (map guard-arity cases)]
      [(∀/C _ E _ _)
       ;; TODO: real Racket just returns `(arity-at-least 0)`
       (cond [(E-arity E) => values] [else (error 'guard-arity "~a" E)])]))

  (: E-arity (case->
              [-->i → (U Natural arity-at-least)]
              [E → Arity]))
  (define E-arity
    (match-lambda
      [(-->i doms _) (shape doms)]
      [(case--> cases) (map E-arity cases)]
      [(-∀/c _ E _) (E-arity E)]
      [E (error 'E-arity "~a" E)]))

  (:* with-negative-party with-positive-party : -l V → V)
  (define with-negative-party
    (match-lambda**
     [(l- (Guarded (Ctx l+ _ ℓₒ ℓ) C α)) (Guarded (Ctx l+ l- ℓₒ ℓ) C α)]
     [(_ V) V]))
  (define with-positive-party
    (match-lambda**
     [(l+ (Guarded (Ctx _ l- ℓₒ ℓ) C α)) (Guarded (Ctx l+ l- ℓₒ ℓ) C α)]
     [(_ V) V]))

  (: make-renamings : (U (Listof Symbol) -formals) W → Renamings)
  (define (make-renamings fml W)
    (define xs (if (-var? fml) (-var-init fml) fml))
    (define-values (W₀ Wᵣ) (if (and (-var? fml) (-var-rest fml))
                               (split-at W (length xs))
                               (values W #f))) 
    (define m
      (for/hash : (Immutable-HashTable γ (Option T)) ([x (in-list xs)] [Vs (in-list W₀)])
        (values (γ:lex x)
                (and (= 1 (set-count Vs))
                     (let ([V (set-first Vs)])
                       (and (T? V) V))))))
    (match fml
      [(-var _ (? values z)) (hash-set m (γ:lex z) #f)]
      [_ m]))

  (: rename : Renamings → (case->
                           [T → (Option T)]
                           [(U T -b) → (Option (U T -b))]))
  ;; Compute renaming in general.
  ;; `#f` means there's no correspinding name
  (define (rename rn)
    (: go (case-> [T → (Option T)]
                  [(U T -b) → (Option (U T -b))]))
    (define go
      (match-lambda
        [(T:@ o Ts)
         (define Ts* (go* Ts))
         (and Ts* (T:@ o Ts*))]
        [(? -b? b) b]
        [(? α? α) (hash-ref rn α (λ () α))]))
    (define go* : ((Listof (U T -b)) → (Option (Listof (U T -b))))
      (match-lambda
        ['() '()]
        [(cons T Ts) (match (go T)
                       [#f #f]
                       [(? values T*) (match (go* Ts)
                                        [#f #f]
                                        [(? values Ts*) (cons T* Ts*)])])]))
    go)

  (: T-root : T:@ → (℘ α))
  (define (T-root T₀)
    (define o-root : (-o → (℘ α))
      (match-lambda
        [(-st-ac 𝒾 i) {set (γ:escaped-field 𝒾 i)}]
        [_ ∅]))
    (let go ([T : (U T -b) T₀])
      (cond [(T:@? T) (apply ∪ (o-root (T:@-_0 T)) (map go (T:@-_1 T)))]
            [(-b? T) ∅]
            [else {set T}])))

  (: ac-Ps : -st-ac (℘ P) → (℘ P))
  (define (ac-Ps ac Ps)
    (for/fold ([Ps* : (℘ P) ∅]) ([P (in-set Ps)])
      (match P
        [(P:St (cons (== ac) acs*) P*)
         (set-add Ps* (if (pair? acs*) (P:St acs* P*) P*))]
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

  (define blur : (case->
                  [V → V]
                  [V^ → V^])
    (match-lambda
      [(-b (app blur-b (? values P))) (-● {set P})]
      [(? set? Vs) (map/set blur Vs)]
      [(and V (not (? set?))) V]))

  (: blur-b : Base → (Option P))
  (define (blur-b b)
    (define-syntax-rule (try-each p? ...)
      (cond [(p? b) 'p?] ... [else #f]))
    (try-each
     exact-positive-integer?
     exact-nonnegative-integer?
     exact-integer?
     integer?
     real?
     number?
     string?
     char?
     regexp?))

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
  )
