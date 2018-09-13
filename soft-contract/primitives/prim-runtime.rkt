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
  (import val^ env^ evl^
          alloc^ compile^
          prover^
          step^ approx^)
  (export prim-runtime^)

  (splicing-let ([TT (list {set -tt})]
                 [FF (list {set -ff})])
    (: implement-predicate : Σ Φ^ -o W → R^)
    (define (implement-predicate Σ Φ^₀ o W)
      (define-values (R+ R-) (split-results Σ (R W Φ^₀) o))
      (define ?res (and (andmap S? W) (list (S:@ o W))))
      ((inst with-2-paths/collapse R) (λ () (split-results Σ (R W Φ^₀) o))
       (λ (Φ^) {set (R (or ?res TT) Φ^)})
       (λ (Φ^) {set (R (or ?res FF) Φ^)}))))

  (define/memoeq (make-total-pred [n : Index]) : (Symbol → ⟦F⟧^)
    (λ (o)
      (λ (W ℓ Φ^ Ξ Σ)
        (cond
          [(equal? n (length W))
           (define ok (ret! (implement-predicate Σ Φ^ o W) Ξ Σ))
           ;; Disallow even "total" predicate on sealed values as a strict enforcement of parametricity
           (define ?er
             (match ((inst findf T^) (λ (T^) (and (set? T^) (set-ormap Sealed? T^))) W)
               [(? set? T^) (r:blm ℓ o '(any/c) (list T^))]
               [#f ∅]))
           {set-add ?er ok}]
          [else (r:blm ℓ o (list (-b n) 'values) W)]))))

  (define alias-table : Alias-Table (make-alias-table #:phase 0))
  (define const-table : Parse-Prim-Table (make-parse-prim-table #:phase 0))
  (define prim-table  : (HashTable Symbol ⟦F⟧^) (make-hasheq))
  (define opq-table   : (HashTable Symbol -●) (make-hasheq))
  (define debug-table : (HashTable Symbol Any) (make-hasheq))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers for some of the primitives
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: W->bs : W → (Option (Listof Base)))
  (define (W->bs W) (and (andmap -b? W) (map -b-unboxed W)))

  
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
     ℓ Symbol Ξ:co Σ
     #:volatile? Boolean
     #:dom (Listof (Pairof V ℓ))
     #:rng W
     #:rng-wrap (Option (Listof (Pairof V ℓ)))
     #:refinements (Listof (List (Listof V) (Option V) (Listof V)))
     #:args R
     → Ξ)
  (define (exec-prim
           ℓ o Ξ Σ
           #:volatile? volatile?
           #:dom doms
           #:rng ranges
           #:rng-wrap ?range-wraps
           #:refinements refinements
           #:args args)
    (define l (ℓ-src ℓ))
    (define ctx* (Ctx l o o ℓ))
    (define ctx (Ctx o l o ℓ))

    (define (no-return?)
      (ormap (match-λ? {singleton-set (-● (singleton-set 'none/c))}) ranges))

    (define (simple-pred?)
      (and (null? refinements)
           (equal? 'boolean? (hash-ref range-table o #f))
           (andmap symbol? (map (inst car V Any) doms))))

    (define (args:behavioral?)
      (for*/or ([Φ^₀ (in-value (R-_1 args))]
                [T (in-list (R-_0 args))]
                [V (in-set (T->V Σ Φ^₀ T))])
        (behavioral? Σ V)))

    (define (mk-rng)
      (F:Make-Prim-Range ctx (and ?range-wraps (map mk-αℓ ?range-wraps)) ranges refinements))
    
    (define Ξ:gen-rng
      (cond [(no-return?)       (K+ (F:Absurd) Ξ)]
            [(simple-pred?)     (K+ (F:Implement-Predicate o) Ξ)]
            [(args:behavioral?) (K+ (F:Havoc-Prim-Args ℓ o) (K+ (mk-rng) Ξ))]
            [else               (K+ (mk-rng) Ξ)]))
    
    (define Ξ:chk-args (K+ (F:Mon*:C ctx* (map mk-αℓ doms)) Ξ:gen-rng))
    (ret! args Ξ:chk-args Σ))

  (: vec-len : T^ → T^)
  (define (vec-len T^)
    (if (set? T^)
        (set-union-map
         (match-lambda
           [(Vect αs) {set (-b (length αs))}]
           [(Vect^ _ Vₙ) Vₙ]
           [(X/G (Vect/C αs) _ _) {set (-b (length αs))}] 
           [_ {set (-● {set 'exact-nonnegative-integer?})}])
         T^)
        (S:@ 'vector-length (list T^))))

  (: mk-res : Φ^ (Listof (℘ P)) -o W → (Values W Φ^))
  (define (mk-res Φ^₀ Ps-list o Wₓ)
    (if (andmap S? Wₓ)
        (let ([Sₐ (S:@ o Wₓ)])
          (match (length Ps-list)
            [1 (values (list Sₐ) (Ψ+ Φ^₀ (car Ps-list) (list Sₐ)))]
            [n (define Sᵢs (for/list : (Listof S) ([i (in-range n)])
                             (S:@ (-st-ac -𝒾-values (assert i index?)) (list Sₐ))))
               (define Φ^* (for/fold ([acc : Φ^ Φ^₀])
                                     ([Sᵢ (in-list Sᵢs)] [Ps (in-list Ps-list)])
                             (Ψ+ acc Ps (list Sᵢ))))
               (values Sᵢs Φ^*)]))
        (values (for/list : (Listof V^) ([Ps (in-list Ps-list)])
                  {set (-● Ps)})
                Φ^₀)))

  (: add-seal : Σ Symbol H -l → Seal/C)
  (define (add-seal Σ x H l)
    (define C (Seal/C x H l))
    (⊔ᵥ! Σ (mk-α (-α:sealed x H)) ∅)
    C)

  (define mk-αℓ : ((Pairof V ℓ) → αℓ)
    (match-lambda [(cons V ℓ) (αℓ (mk-α (-α:imm V)) ℓ)]))

  ;; Eta-expand to get aroudn undefined and init-depend
  (: r:ret! : ((U R R^) Ξ:co Σ → Ξ:co))
  (: r:blm : (ℓ -l (Listof (U V V^)) (U W W^) → (℘ Blm)))
  (: r:split-results : Σ R P → (Values R^ R^))
  (: r:with-2-paths/collapse
     (∀ (X) (→ (Values R^ R^)) (Φ^ → (℘ X)) (Φ^ → (℘ X)) → (℘ X)))
  (define (r:ret! R Ξ Σ) (ret! R Ξ Σ))
  (define (r:with-2-paths/collapse e t f) (with-2-paths/collapse e t f))
  (define (r:split-results Σ R P) (split-results Σ R P))
  (define (r:blm ℓ+ lo C V) (blm ℓ+ lo C V))

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
