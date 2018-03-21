#lang typed/racket/base

(provide prim-runtime@)
(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         racket/sequence
         racket/splicing
         syntax/parse/define
         typed/racket/unit
         set-extras
         unreachable
         typed-racket-hacks
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prim-runtime@
  (import val^ sto^ env^ evl^
          alloc^ compile^
          prover^
          step^)
  (export prim-runtime^)

  (splicing-let ([TT (list {set -tt})]
                 [FF (list {set -ff})]
                 [?? (list {set (-● {set 'boolean?})})])
    (: implement-predicate : Σ Φ^ -o W → R^)
    (define (implement-predicate Σ Φ^₀ o W)
      ((inst with-3-paths R) (λ () (partition-sats Σ Φ^₀ o W))
        (λ (Φ^) {set (R TT Φ^)})
        (λ (Φ^) {set (R FF Φ^)})
        (λ (Φ^) {set (R ?? Φ^)}))))
  

  (define/memoeq (make-total-pred [n : Index]) : (Symbol → ⟦F⟧^)
    (λ (o)
      (λ (W ℓ Φ^ Ξ Σ)
        (cond
          [(equal? n (length W))
           (define ok (ret! (implement-predicate Σ Φ^ o W) Ξ Σ))
           ;; Disallow even "total" predicate on sealed values as a strict enforcement of parametricity
           (define ?er
             (match (for/or : (Option V^) ([V (in-list W)] #:when (sequence-ormap Sealed? V))
                      V)
               [(? set? V) {set (Blm/simp ℓ o '(any/c) (list V))}]
               [#f ∅]))
           {set-add ?er ok}]
          [else {set (Blm/simp ℓ o (list (-b n) 'values) W)}]))))

  (define alias-table : Alias-Table (make-alias-table #:phase 0))
  (define const-table : Parse-Prim-Table (make-parse-prim-table #:phase 0))
  (define prim-table  : (HashTable Symbol ⟦F⟧^) (make-hasheq))
  (define opq-table   : (HashTable Symbol -●) (make-hasheq))
  (define debug-table : (HashTable Symbol Any) (make-hasheq))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers for some of the primitives
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: W->bs : W → (Option (Listof Base)))
  (define (W->bs W)
    (foldr (λ ([V^ : V^] [?bs : (Option (Listof Base))])
             (and ?bs
                  (= 1 (set-count V^))
                  (-b? (set-first V^))
                  (cons (-b-unboxed (assert (set-first V^) -b?)) ?bs)))
           '()
           W))

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Implication and Exclusion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define implication-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
  (define exclusion-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
  (define implication-table⁻¹ : (HashTable Symbol (℘ Symbol)) (make-hasheq))

  (: add-implication! : Symbol Symbol → Void)
  ;; Extend implication table and take care of transitivity
  (define (add-implication! p q)
    (unless (map-has? implication-table p q)
      (map-add! implication-table   p q #:eq? #t)
      (map-add! implication-table⁻¹ q p #:eq? #t)
      ;; implication is reflexive
      (add-implication! p p)
      (add-implication! q q)
      ;; implication is transitive
      (for ([q* (in-set (get-weakers q))])
        (add-implication! p q*))
      (for ([p₀ (in-set (get-strongers p))])
        (add-implication! p₀ q))
      ;; (r → ¬q) and (q₀ → q) implies r → ¬q₀
      (for* ([r (in-set (get-exclusions q))])
        (add-exclusion! p r))))

  (: add-exclusion! : Symbol Symbol → Void)
  ;; Extend exclusion table and take care of inferring existing implication
  (define (add-exclusion! p q)
    (unless (map-has? exclusion-table p q)
      (map-add! exclusion-table p q #:eq? #t)
      ;; (p → ¬q) and (q₀ → q) implies (p → ¬q₀)
      (for ([q₀ (in-set (get-strongers q))])
        (add-exclusion! p q₀))
      (for ([p₀ (in-set (get-strongers p))])
        (add-exclusion! p₀ q))
      ;; exclusion is symmetric
      (add-exclusion! q p)))

  (:* get-weakers get-strongers get-exclusions : Symbol → (℘ Symbol))
  (define (get-weakers    p) (hash-ref implication-table   p mk-∅eq))
  (define (get-strongers  p) (hash-ref implication-table⁻¹ p mk-∅eq))
  (define (get-exclusions p) (hash-ref exclusion-table     p mk-∅eq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Range
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define range-table : (HashTable Symbol Symbol) (make-hasheq))
  (define partial-prims : (HashTable Symbol Natural) (make-hasheq))

  (: set-range! : Symbol Symbol → Void)
  (define (set-range! o r) (hash-set-once! range-table o r))

  (: set-partial! : Symbol Natural → Void)
  (define (set-partial! o n) (hash-set! partial-prims o n))

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Arity
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define arity-table : (HashTable Symbol Arity)
    (make-hasheq (list (cons 'void (arity-at-least 0))
                       (cons 'values (arity-at-least 0))
                       (cons 'hash-ref (ann (list 2 3) Arity)))))

  (: update-arity! : Symbol Arity → Void)
  (define (update-arity! o a)
    (cond [(hash-ref arity-table o #f) =>
           (λ ([a₀ : Arity])
             (unless (arity-includes? a₀ a)
               (hash-set! arity-table o (normalize-arity (list a₀ a)))))]
          [else
           (hash-set! arity-table o a)]))

  (: add-const! : Identifier -prim → Void)
  (define (add-const! x v)
    (cond [(parse-prim-table-ref const-table x (λ () #f)) =>
           (λ ([v₀ : -prim])
             (error 'add-const! "~a ↦ ~a, attempt to set to ~a"
                    (syntax-e x) v₀ v))]
          [else (parse-prim-table-set! const-table x v)]))

  (: add-alias! : Identifier Identifier → Void)
  (define (add-alias! x y)
    (cond [(alias-table-ref alias-table x (λ () #f)) =>
           (λ ([y₀ : Identifier])
             (error 'add-alias! "~a ↦ ~a, attempt to set to ~a"
                    (syntax-e x) (syntax-e y₀) (syntax-e y)))]
          [else (alias-table-set! alias-table x y)]))

  (: make-listof : Boolean V ℓ → V)
  (define (make-listof flat? Cₕ ℓ)
    (define x (format-symbol "gen-listof-~a" (mk-α (-α:imm Cₕ))))
    (X/C (mk-α (-α:imm:listof x Cₕ ℓ))))

  (: make-static-listof : Symbol (→ (Values Boolean V ℓ)) → V)
  (define make-static-listof
    (let ([cache : (Mutable-HashTable Symbol V) (make-hasheq)])
      (λ (tag mk-V)
        (hash-ref! cache tag (λ () (call-with-values mk-V make-listof))))))

  (: make-∀/c : Symbol (Listof Symbol) -e Ρ → V)
  (define make-∀/c
    (let ([e-cache : (Mutable-HashTable -e ⟦E⟧) (make-hash)])
      (λ (src xs e Ρ)
        (define ⟦E⟧ (hash-ref! e-cache e (λ () (↓ₑ src e))))
        (∀/C xs ⟦E⟧ Ρ))))

  (: make-static-∀/c : Symbol Symbol (Listof Symbol) (→ -e) → V)
  (define make-static-∀/c
    (let ([cache : (Mutable-HashTable Symbol V) (make-hasheq)])
      (λ (tag src xs mk-e)
        (hash-ref! cache tag (λ () (make-∀/c src xs (mk-e) ⊥Ρ))))))

  (: exec-prim :
     ℓ (Intersection Symbol -o) Φ^ Ξ:co Σ
     #:volatile? Boolean
     #:dom (Listof (Pairof V ℓ))
     #:rng W
     #:rng-wrap (Option (Listof (Pairof V ℓ)))
     #:refinements (Listof (List (Listof V) (Option V) (Listof V)))
     #:args W
     → Ξ)
  (define (exec-prim
           ℓ o Φ^ Ξ Σ
           #:volatile? volatile?
           #:dom doms
           #:rng ranges
           #:rng-wrap ?range-wraps
           #:refinements refinements
           #:args args)
    (define l (ℓ-src ℓ))
    (define ctx* (Ctx l o o ℓ))
    (define ctx (Ctx o l o ℓ))
    (define Ξ:chk-args-done
      (cond
        [(and (null? refinements)
              (equal? 'boolean? (hash-ref range-table o #f))
              (andmap symbol? (map (inst car V Any) doms)))
         (K+ (F:Implement-Predicate o) Ξ)]
        [else
         (define Ξ:mk-rng
           (K+ (F:Make-Prim-Range ctx (and ?range-wraps (map mk-αℓ ?range-wraps)) ranges refinements) Ξ))
         (K+ (F:Maybe-Havoc-Prim-Args ℓ o) Ξ:mk-rng)]))
    (define Ξ:chk-args (K+ (F:Mon*:C ctx* (map mk-αℓ doms)) Ξ:chk-args-done))
    (ret! (R args Φ^) Ξ:chk-args Σ)
    #|
    (define l (ℓ-src ℓ))
    (define ctx* (Ctx l o o ℓ))
    (define ctx  (Ctx o l o ℓ))

    (define ⟦k⟧:chk-args-done
      (let ([no-return?
             (for/or : Boolean ([rng (in-list ranges)])
               (match rng
                 [(singleton-set (-● (singleton-set 'none/c))) #t]
                 [_ #f]))])
        (cond
          [no-return? (absurd∷ ⟦k⟧)]
          [(and (null? refinements)
                (equal? 'boolean? (hash-ref range-table o #f))
                (andmap symbol? (map (inst car -V Any) doms)))
           (implement-predicate∷ o ⟦k⟧)]
          [else
           (define ⟦k⟧:mk-rng
             (make-prim-range∷ ctx (and ?range-wraps (map mk-⟪α⟫ℓ ?range-wraps)) ranges refinements ⟦k⟧))
           (maybe-havoc-prim-args∷ ℓ o ⟦k⟧:mk-rng)])))
    (define ⟦k⟧:chk-args (mon*.c∷ ctx* (map mk-⟪α⟫ℓ doms) ⟦k⟧:chk-args-done))
    (⟦k⟧:chk-args args H φ Σ)
    |#)

  (: vec-len : V^ → V^)
  (define (vec-len Vs)
    (for/union : V^ ([V (in-set Vs)])
      (match V
        [(Vect αs) {set (-b (length αs))}]
        [(Vect^ _ Vₙ) Vₙ]
        [(X/G (Vect/C αs) _ _) {set (-b (length αs))}]
        [(? S? V) {set (S:@ 'vector-length (list V))}]
        [_ {set (-● {set 'exact-nonnegative-integer?})}])))

  (: mk-res : (℘ P) -o W → V^)
  (define (mk-res Ps o Wₓ)
    (cond
      [(andmap (λ ([V^ : V^]) (for/and : Boolean ([V (in-set V^)]) (S? V))) Wₓ)
       (define args : (℘ (Listof S))
         (let go ([Wₓ : W Wₓ])
           (match Wₓ
             ['() {set '()}]
             [(cons V Wₓ*)
              (define rst (go Wₓ*))
              (for*/set : (℘ (Listof S)) ([S₁ (in-set V)] [Sᵣ (in-set rst)])
                (cons (assert S₁ S?) Sᵣ))])))
       (for/set : (℘ S) ([arg (in-set args)])
         (S:@ o arg))]
      [else {set (-● Ps)}]))

  
  #|
  (: r:φ+/-pV^ : -σ -φ -h -V^ * → (Values (℘ -φ) (℘ -φ)))
  (define (r:φ+/-pV^ σ φ o . Vs)
    (apply φ+/-pV^ σ φ o Vs))

  
  |#

  (: add-seal : Σ Symbol H -l → Seal/C)
  (define (add-seal Σ x H l)
    (define C (Seal/C x H l))
    (⊔ᵥ! Σ (mk-α (-α:sealed x H)) ∅)
    C)

  (define mk-αℓ : ((Pairof V ℓ) → αℓ)
    (match-lambda [(cons V ℓ) (αℓ (mk-α (-α:imm V)) ℓ)]))

  ;; Eta-expand to get aroudn undefined and init-depend
  (: r:ret! : (U R R^) Ξ:co Σ → Ξ:co)
  (: r:plausible-splits : Σ Φ^ P W → (Values Φ^ Φ^))
  (: r:with-2-paths
     (∀ (X) (→ (Values Φ^ Φ^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
  (define (r:ret! R Ξ Σ) (ret! R Ξ Σ))
  (define (r:with-2-paths e t f) (with-2-paths e t f))
  (define (r:plausible-splits Σ Φ^ P W) (plausible-splits Σ Φ^ P W))

  #|
  (: t.@/simp : -o (Listof -t) → -t)
  (define t.@/simp
    (match-lambda**
     [('+ (list (? -b? b) (-t.@ '- (list t b)))) t]
     [('+ (list (-b 0) t)) t]
     [('+ (list t (-b 0))) t]
     [('- (list t (-b 0))) t]
     [('* (list t (-b 1))) t]
     [('* (list (-b 1) t)) t]
     [('= (list t t)) -tt]
     [('any/c _) -tt]
     [('none/c _) -ff]
     [(o ts) (-t.@ o ts)]))
  |#
  )
