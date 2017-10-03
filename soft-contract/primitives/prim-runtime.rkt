#lang typed/racket/base

(provide prim-runtime@)
(require racket/match
         racket/set
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
  (import ast-pretty-print^ proof-system^ local-prover^ widening^
          pc^ val^ sto^ compile^ env^ kont^)
  (export prim-runtime^)
  (init-depend val^)

  (: unchecked-ac : -σ -Γ -st-ac -W¹ → (℘ -W¹))
  ;; unchecked struct accessor, assuming the value is already checked to be the right struct.
  ;; This is only for use internally, so it's safe (though imprecise) to ignore field wraps
  (define (unchecked-ac σ Γ ac W)
    (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
    (match-define (-W¹ V s) W)
    (match-define (-st-ac 𝒾 i) ac)
    (define φs Γ)
    (define s* (?t@ ac s))
    (let go ([V : -V V])
      (match V
        [(-St (== 𝒾) αs)
         (for/set: : (℘ -W¹) ([V* (in-set (σ@ σ (list-ref αs i)))]
                              #:when (plausible-V-t? φs V* s*))
           (-W¹ V* s*))]
        [(-St* (-St/C _ (== 𝒾) _) α _)
         (cond [(seen-has? α) ∅]
               [else
                (seen-add! α)
                (for/union : (℘ -W¹) ([V (in-set (σ@ σ α))]
                                      #:when (plausible-V-t? φs V s))
                           (go V))])]
        [(? -●?) {set (-W¹ (+●) s*)}]
        [_ ∅])))

  (: implement-predicate : -σ -Γ Symbol (Listof -W¹) → (Values -V -?t))
  (define (implement-predicate σ Γ o Ws)
    (define V
      (case (apply Γ⊢oW σ Γ o Ws)
        [(✓) -tt]
        [(✗) -ff]
        [(?) (+● 'boolean?)]))
    (values V (apply ?t@ o (map -W¹-t Ws))))

  (define/memoeq (make-total-pred [n : Index]) : (Symbol → -⟦f⟧)
    (λ (o)
      (λ (ℓ Ws $ Γ H Σ ⟦k⟧)
        (cond [(equal? n (length Ws))
               (define ok
                 (let-values ([(Vₐ tₐ) (implement-predicate (-Σ-σ Σ) Γ o Ws)])
                   (⟦k⟧ (-W (list Vₐ) tₐ) $ Γ H Σ)))
               (define er
                 (match (ormap
                         (match-lambda
                           [(-W¹ (? -Sealed? V) _) V]
                           [_ #f])
                         Ws)
                   [(? -Sealed? V*)
                    (define blm (-blm (ℓ-src ℓ) o '(any/c) (list V*) ℓ))
                    (⟦k⟧ blm $ Γ H Σ)]
                   [_ ∅]))
               (∪ ok er)]
              [else
               (⟦k⟧ (blm-arity ℓ o n (map -W¹-V Ws)) $ Γ H Σ)]))))

  (define alias-table : Alias-Table (make-alias-table #:phase 0))
  (define const-table : Parse-Prim-Table (make-parse-prim-table #:phase 0))
  (define prim-table  : (HashTable Symbol -⟦f⟧) (make-hasheq))
  (define opq-table   : (HashTable Symbol -●) (make-hasheq))
  (define debug-table : (HashTable Symbol Any) (make-hasheq))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers for some of the primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: ts->bs : (Listof -?t) → (Option (Listof Base)))
  (define (ts->bs ts)
    (foldr (λ ([t : -?t] [?bs : (Option (Listof Base))])
             (and ?bs (-b? t) (cons (-b-unboxed t) ?bs)))
           '()
           ts))

  (: Ws->bs : (Listof -W¹) → (Option (Listof Base)))
  (define (Ws->bs Ws) (ts->bs (map -W¹-t Ws)))

  
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

  (: arity-check/handler (∀ (X) (-Γ → (℘ X)) (-Γ → (℘ X)) -Γ -W¹ Arity → (℘ X)))
  (define (arity-check/handler t f Γ W arity)
    (match-define (-W¹ V s) W) ; ignore `Γ` and `s` for now
    (define (on-t) (t Γ)) ; TODO
    (define (on-f) (f Γ)) ; TODO
    (cond [(V-arity V) =>
           (λ ([a : Arity])
             ((if (arity-includes? a arity) t f) Γ))]
          [else (∪ (t Γ) (f Γ))]))

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

  (: make-listof : Boolean -V ℓ → -V)
  (define (make-listof flat? Cₕ ℓ)
    (define x (format-symbol "gen-listof-~a" (-α->⟪α⟫ (-α.imm Cₕ))))
    (-x/C (-α->⟪α⟫ (-α.imm-listof x Cₕ ℓ))))

  (: make-static-listof : Symbol (→ (Values Boolean -V ℓ)) → -V)
  (define make-static-listof
    (let ([cache : (Mutable-HashTable Symbol -V) (make-hasheq)])
      (λ (tag mk-V)
        (hash-ref! cache tag (λ () (call-with-values mk-V make-listof))))))

  (: make-∀/c : Symbol (Listof Symbol) -e -ρ → -V)
  (define make-∀/c
    (let ([e-cache : (Mutable-HashTable -e -⟦e⟧) (make-hash)])
      (λ (src xs e ρ)
        (define ⟦e⟧ (hash-ref! e-cache e (λ () (↓ₑ src e))))
        (-∀/C xs ⟦e⟧ ρ))))

  (: make-static-∀/c : Symbol Symbol (Listof Symbol) (→ -e) → -V)
  (define make-static-∀/c
    (let ([cache : (Mutable-HashTable Symbol -V) (make-hasheq)])
      (λ (tag src xs mk-e)
        (hash-ref! cache tag (λ () (make-∀/c src xs (mk-e) ⊥ρ))))))

  (: exec-prim :
     -$ -Γ -H -Σ -⟦k⟧
     ℓ (Intersection Symbol -o)
     #:volatile? Boolean
     #:dom (Listof (Pairof -V ℓ))
     #:rng (Listof -V)
     #:rng-wrap (Option (Listof (Pairof -V ℓ)))
     #:refinements (Listof (List (Listof -V) (Option -V) (Listof -V)))
     #:args (Listof -W¹)
     → (℘ -ς))
  (define (exec-prim
           $ Γ H Σ ⟦k⟧
           ℓ o
           #:volatile? volatile?
           #:dom doms
           #:rng ranges
           #:rng-wrap ?range-wraps
           #:refinements refinements
           #:args args
           )
    (define-values (V-args t-args) (unzip-by -W¹-V -W¹-t args))
    (define t-ans (if volatile? ℓ (apply ?t@ o t-args)))
    (define l (ℓ-src ℓ))
    (define ctx* (-ctx l o o ℓ))
    (define ctx (-ctx o l o ℓ))

    (define ⟦k⟧:chk-args-done
      (let ([no-return?
             (for/or : Boolean ([rng (in-list ranges)])
               (match rng
                 [(-● ps) (∋ ps 'none/c)]
                 [_ #f]))])
        (cond
          [no-return? (absurd∷ ⟦k⟧)]
          [(and (match? ranges (list (-● (== {set 'boolean?}))))
                (andmap symbol? (map (inst car -V Any) doms)))
           (implement-predicate∷ o ⟦k⟧)]
          [else
           (define ⟦k⟧:wrap-range
             (if ?range-wraps
                 (mon*.c∷ ctx (map alloc ?range-wraps) t-ans ⟦k⟧)
                 ⟦k⟧))
           (on-prim-args-checked∷ ℓ refinements (-W ranges t-ans) ⟦k⟧:wrap-range)])))
    (define ⟦k⟧:chk-args (mon*.c∷ ctx* (map alloc doms) #f ⟦k⟧:chk-args-done))
    (⟦k⟧:chk-args (-W V-args (apply ?t@ 'values t-args)) $ Γ H Σ))

  ;; Eta-expand to prevent messing with init-depend
  (: mk-● : -h * → -●)
  (define (mk-● . xs) (apply +● xs))
  (: r:Γ⊢oW/handler : ((→ (℘ -ς)) (→ (℘ -ς)) -σ -Γ -o -W¹ * → (℘ -ς)))
  (define (r:Γ⊢oW/handler on-t on-f σ Γ o . Ws)
    (apply Γ⊢oW/handler on-t on-f σ Γ o Ws))

  (: add-seal! : -Σ Symbol -H -l → -Seal/C)
  (define (add-seal! Σ x H l)
    (define C (-Seal/C x H l))
    (σ⊕Vs! Σ (-α->⟪α⟫ (-α.sealed x H)) ∅)
    C)

  (define alloc : ((Pairof -V ℓ) → -⟪α⟫ℓ)
    (match-lambda [(cons V ℓ) (-⟪α⟫ℓ (-α->⟪α⟫ (-α.imm V)) ℓ)]))
  )
