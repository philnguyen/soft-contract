#lang typed/racket/base

(provide val@)

(require typed/racket/unit
         racket/match
         racket/set
         racket/splicing
         (only-in racket/function curry)
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

  (splicing-local
      ((define (D⊔ [Σ : Σ] [D₁ : D] [D₂ : D])
         (cond [(and (set? D₁) (set? D₂)) (V⊔ D₁ D₂)]
               [(equal? D₁ D₂) D₁]
               [else (V⊔ (unpack D₁ Σ) (unpack D₂ Σ))]))
       (: W⊔ : Σ W W → W)
       (define (W⊔ Σ W₁ W₂) (map (curry D⊔ Σ) W₁ W₂)))
    (: collapse-W^ : Σ W^ → W)
    (define (collapse-W^ Σ Ws) (set-fold (curry W⊔ Σ) (set-first Ws) (set-rest Ws))))

  (define Ctx-with-site : (Ctx ℓ → Ctx)
    (match-lambda** [((Ctx l+ l- ℓₒ _) ℓ) (Ctx l+ l- ℓₒ ℓ)]))

  (define Ctx-with-origin : (Ctx ℓ → Ctx)
    (match-lambda** [((Ctx l+ l- _ ℓ) ℓₒ) (Ctx l+ l- ℓₒ ℓ)]))

  (define Ctx-flip : (Ctx → Ctx)
    (match-lambda [(Ctx l+ l- lo ℓ) (Ctx l- l+ lo ℓ)]))

  (: C-flat? : (U V V^) Σ → Boolean)
  ;; Check whether contract is flat, assuming it's already a contract
  (define (C-flat? C Σ)
    (define-set seen : α #:mutable? #t)
    (: go-T : (U T -prim α) → Boolean)
    (define (go-T T)
      (cond [(-prim? T) #t]
            [(T? T) (go-V^ (unpack T Σ))]
            [else (go-α T)]))

    (: go-α : α → Boolean)
    (define (go-α α)
      (cond [(seen-has? α) #t]
            [else (seen-add! α)
                  (S-andmap go-V^ go-T (Σ@/raw α Σ))]))

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
        [(or (? Clo?) (? -λ?) (Guarded _ (? Fn/C?) _) (? -prim?) (? Case-Clo?)) #t]
        [(Rec/C α) (go-α α)]
        [(? ∀/C?) #f]
        [(? Seal/C?) #f]
        [(? P?) #t]
        [(? α? α) (go-α α)]
        [V (error 'C-flat? "unexpected: ~a" V)]))

    (if (set? C) (go-V^ C) (go-V C)))

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
    (let go : Boolean ([T : (U -prim T) T₀])
      (match T
        [(γ:lex x) (∋ xs x)]
        [(T:@ _ Ts) (ormap go Ts)]
        [_ #f])))

  (define T:@/simp : (K (Listof (U T -prim)) → (U -prim T))
    (match-lambda**
     [((-st-ac 𝒾 i) (list (T:@ (-st-mk 𝒾) Ts))) (list-ref Ts i)]
     [((-st-mk 𝒾) (list (T:@ (-st-ac 𝒾s #{ks : (Listof Index)}) (list #{Ts : (Listof (U -prim T))})) ...))
      #:when (and (pair? Ts)
                  (counting-up? ks)
                  (all-same? 𝒾 𝒾s)
                  (all-same? (car Ts) (cdr Ts)))
      (car Ts)]
     [('+ (list (-b (? number? #{xs : (Listof Number)})) ...)) (-b (apply + xs))]
     [('- (list (-b (? number? x₀)) (-b (? number? #{xs : (Listof Number)})) ...)) (-b (apply - x₀ xs))]
     [('* (list (-b (? number? #{xs : (Listof Number)})) ...)) (-b (apply * xs))]
     [('/ (list (-b (? number? x₀)) (-b (? number? #{xs : (Listof Number)})) ...)) (-b (apply / x₀ xs))]
     [('add1 (list (-b (? number? x)))) (-b (add1 x))]
     [('sub1 (list (-b (? number? x)))) (-b (sub1 x))]
     [(K Ts) (T:@ K Ts)]))

  (: counting-up? : (Listof Integer) → Boolean)
  (define (counting-up? ns)
    (for/and : Boolean ([(n i) (in-indexed ns)])
      (equal? n i)))

  (: all-same? : Any (Listof Any) → Boolean)
  (define (all-same? x xs)
    (or (null? xs) (and (equal? x (car xs)) (all-same? x (cdr xs)))))

  ;; Check if the pair `T S*` encodes a proposition
  ;; This is a temporary HACK that should eventually be obsolete by refactoring
  (define prop? : (T S* → Boolean)
    (match-lambda**
     [((T:@ (or (? K:≡?) (? K:≤?) (? K:=?) (? γ:top?)) _) (or (? -b?) {singleton-set (? -b?)})) #t]
     [(_ _) #f]))

  (: ListOf : γ:imm:listof → V)
  (define (ListOf α)
    (match-define (γ:imm:listof x Cₑ ℓ) α)
    (define Cₚ (St/C (γ:imm:blob:st (vector-immutable {set Cₑ} {set (Rec/C α)})
                                    (ℓ-with-id ℓ 'imm:pair)
                                    -𝒾-cons)))
    (Or/C (γ:imm 'null?) (γ:imm Cₚ) (ℓ-with-id ℓ 'imm:or)))

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

  (: V⊓ : V^ V^ → (Option V^))
  (define (V⊓ Vs₁ Vs₂)
    (: set-extract-single (∀ (X T) (X → Boolean : T) (℘ X) → (Option T)))
    (define (set-extract-single p? xs)
      (match (set-filter p? xs)
        [{singleton-set t} t]
        [(? set-empty?) #f]
        [_ !!!]))
    (define ●*
      (match* ((set-extract-single -●? Vs₁) (set-extract-single -●? Vs₂))
        [((-● Ps) (-● Qs))
         (define Ps*
           (for/fold ([Ps : (℘ P) Ps]) ([Q (in-set Qs)])
             (refine-Ps Ps Q)))
         {set (-● Ps*)}]
        [((? values V₁) #f) {set V₁}]
        [(#f (? values V₂)) {set V₂}]
        [(#f #f) ∅]))
    (define Vs* (∪ (∩ Vs₁ Vs₂) ●*))
    (and (not (set-empty? Vs*)) Vs*))

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
      (eq? '✓ (sat ⊥Σ P b^))))

  (: Ps⇒Ps? : (℘ P) (℘ P) → Boolean)
  (define (Ps⇒Ps? Ps Qs)
    (for/and : Boolean ([Q (in-set Qs)])
      (for/or : Boolean ([P (in-set Ps)])
        (eq? '✓ (P⊢P P Q)))))

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
