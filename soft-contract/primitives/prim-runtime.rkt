#lang typed/racket/base

(provide prim-runtime@)
(require racket/match
         racket/set
         racket/sequence
         syntax/parse/define
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../reduction/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prim-runtime@
  (import ast-pretty-print^ proof-system^ widening^
          path^ val^ sto^ compile^ env^ kont^)
  (export prim-runtime^)
  (init-depend val^)

  (: implement-predicate : -σ -φ -o (Listof -V^) → -V^)
  (define (implement-predicate σ φ o Vs)
    (case (apply p∋V^ σ φ o Vs)
      [(✓) {set -tt}]
      [(✗) {set -ff}]
      [(?) (mk-res {set 'boolean?} o Vs)]))

  (define/memoeq (make-total-pred [n : Index]) : (Symbol → -⟦f⟧)
    (λ (o)
      (λ (ℓ Vs H φ Σ ⟦k⟧)
        (cond [(equal? n (length Vs))
               (define ok (⟦k⟧ (list (implement-predicate (-Σ-σ Σ) φ o Vs)) H φ Σ))
               (define er
                 (match (for/or : (Option -V^) ([V (in-list Vs)]
                                                #:when (sequence-ormap -Sealed? V))
                          V)
                   [(? set? V^)
                    (define blm (blm/simp (ℓ-src ℓ) o '(any/c) (list V^) ℓ))
                    (⟦k⟧ blm H φ Σ)]
                   [_ ∅]))
               (∪ ok er)]
              [else
               (⟦k⟧ (blm-arity ℓ o n Vs) H φ Σ)]))))

  (define alias-table : Alias-Table (make-alias-table #:phase 0))
  (define const-table : Parse-Prim-Table (make-parse-prim-table #:phase 0))
  (define prim-table  : (HashTable Symbol -⟦f⟧) (make-hasheq))
  (define opq-table   : (HashTable Symbol -●) (make-hasheq))
  (define debug-table : (HashTable Symbol Any) (make-hasheq))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers for some of the primitives
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: Vs->bs : (Listof -V^) → (Option (Listof Base)))
  (define (Vs->bs Vs)
    (foldr (λ ([V^ : -V^] [?bs : (Option (Listof Base))])
             (and ?bs
                  (= 1 (set-count V^))
                  (-b? (set-first V^))
                  (cons (-b-unboxed (assert (set-first V^) -b?)) ?bs)))
           '()
           Vs))

  
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
                    (syntax-e x) (show-e v₀) (show-e v)))]
          [else (parse-prim-table-set! const-table x v)]))

  (: add-alias! : Identifier Identifier → Void)
  (define (add-alias! x y)
    (cond [(alias-table-ref alias-table x (λ () #f)) =>
           (λ ([y₀ : Identifier])
             (error 'add-alias! "~a ↦ ~a, attempt to set to ~a"
                    (syntax-e x) (syntax-e y₀) (syntax-e y)))]
          [else (alias-table-set! alias-table x y)]))

  (: make-listof : Boolean -U ℓ → -U)
  (define (make-listof flat? Cₕ ℓ)
    (define x (format-symbol "gen-listof-~a" (-α->⟪α⟫ (-α.imm Cₕ))))
    (-x/C (-α->⟪α⟫ (-α.imm-listof x Cₕ ℓ))))

  (: make-static-listof : Symbol (→ (Values Boolean -U ℓ)) → -U)
  (define make-static-listof
    (let ([cache : (Mutable-HashTable Symbol -U) (make-hasheq)])
      (λ (tag mk-V)
        (hash-ref! cache tag (λ () (call-with-values mk-V make-listof))))))

  (: make-∀/c : Symbol (Listof Symbol) -e -ρ → -U)
  (define make-∀/c
    (let ([e-cache : (Mutable-HashTable -e -⟦e⟧) (make-hash)])
      (λ (src xs e ρ)
        (define ⟦e⟧ (hash-ref! e-cache e (λ () (↓ₑ src e))))
        (-∀/C xs ⟦e⟧ ρ))))

  (: make-static-∀/c : Symbol Symbol (Listof Symbol) (→ -e) → -U)
  (define make-static-∀/c
    (let ([cache : (Mutable-HashTable Symbol -U) (make-hasheq)])
      (λ (tag src xs mk-e)
        (hash-ref! cache tag (λ () (make-∀/c src xs (mk-e) ⊥ρ))))))

  (: exec-prim :
     -H -φ -Σ -⟦k⟧
     ℓ (Intersection Symbol -o)
     #:volatile? Boolean
     #:dom (Listof (Pairof -U ℓ))
     #:rng (Listof -V^)
     #:rng-wrap (Option (Listof (Pairof -U ℓ)))
     #:refinements (Listof (List (Listof -U) (Option -U) (Listof -U)))
     #:args (Listof -V^)
     → (℘ -ς))
  (define (exec-prim
           H φ Σ ⟦k⟧
           ℓ o
           #:volatile? volatile?
           #:dom doms
           #:rng ranges
           #:rng-wrap ?range-wraps
           #:refinements refinements
           #:args args)
    (define l (ℓ-src ℓ))
    (define ctx* (-ctx l o o ℓ))
    (define ctx  (-ctx o l o ℓ))

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
    (⟦k⟧:chk-args args H φ Σ))

  (: vec-len : -σ -φ -V^ → -V^)
  (define (vec-len σ φ V^)
    (for/union : -V^ ([V (in-set V^)])
      (match V
        [(-Vector αs) {set (-b (length αs))}]
        [(-Vector^ _ Vₙ) Vₙ]
        [(-Vector/guard (-Vector/C αs) _ _) {set (-b (length αs))}]
        [(? -t? V) {set (-t.@ 'vector-length (list V))}]
        [_ {set (-● {set 'exact-nonnegative-integer?})}])))

  (: r:φ+/-pV^ : -σ -φ -h -V^ * → (Values (℘ -φ) (℘ -φ)))
  (define (r:φ+/-pV^ σ φ o . Vs)
    (apply φ+/-pV^ σ φ o Vs))

  (: mk-res : (℘ -h) -o (Listof -V^) → -V^)
  (define (mk-res ps o Vs)
    (cond
      [(andmap (λ ([V^ : -V^]) (for/and : Boolean ([V (in-set V^)]) (-t? V))) Vs)
       (define args : (℘ (Listof -t))
         (let go ([Vs : (Listof -V^) Vs])
           (match Vs
             ['() {set '()}]
             [(cons V Vs*)
              (define rst (go Vs*))
              (for*/set: : (℘ (Listof -t)) ([t₁ (in-set V)] [tᵣ (in-set rst)])
                (cons (assert t₁ -t?) tᵣ))])))
       (for/set: : (℘ -t) ([arg (in-set args)])
         (t.@/simp o arg))]
      [else
       {set (-● ps)}]))

  (: add-seal : -Σ -φ Symbol -H -l → (Values -Seal/C -φ))
  (define (add-seal Σ φ x H l)
    (define C (-Seal/C x H l))
    (values C (alloc Σ φ (-α->⟪α⟫ (-α.sealed x H)) ∅)))

  (define mk-⟪α⟫ℓ : ((Pairof -U ℓ) → -⟪α⟫ℓ)
    (match-lambda [(cons V ℓ) (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm V)) ℓ)]))

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
  )
