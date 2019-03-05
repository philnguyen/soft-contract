#lang typed/racket/base

(provide prim-runtime@)
(require racket/match
         (except-in racket/set for/set for*/set for/seteq for*/seteq)
         (only-in racket/list split-at make-list)
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
         "../execution/signatures.rkt"
         "../signatures.rkt"
         "signatures.rkt")

(define-unit prim-runtime@
  (import cache^ val^ sto^
          prover^
          exec^ mon^ hv^)
  (export prim-runtime^)

  (define/memoeq (make-total-pred [n : Index]) : (Symbol → ⟦O⟧)
    (λ (o)
      (define ℓ:o (loc->ℓ (loc o 0 0 '())))
      (λ (Σ ℓ W)
        (cond
          [(equal? n (length W))
           (define-values (r es₀) (implement-predicate Σ o W))
           ;; Disallow even "total" predicate on sealed values as a strict enforcement of parametricity
           (define es₁
             (for*/set: : (℘ Err) ([Vs (in-list W)] [V (in-set (unpack Vs Σ))] #:when (Sealed? V))
               (match-define (Sealed (α:dyn (β:sealed x _) _)) V)
               (Err:Sealed x ℓ)))
           (values r (∪ es₀ es₁))]
          [else (err (Err:Arity o n ℓ))]))))

  (: implement-predicate : Σ -o W → (Values R (℘ Err)))
  (define (implement-predicate Σ o W)
    (with-split-Σ Σ o W
      (λ (_ ΔΣ) (just -tt ΔΣ))
      (λ (_ ΔΣ) (just -ff ΔΣ))))

  (: W->bs : W → (Option (Listof Base)))
  (define W->bs
    (match-lambda
      ['() '()]
      [(cons {singleton-set (-b b)} W)
       (match (W->bs W)
         [(? values bs) (cons b bs)]
         [#f #f])]
      [_ #f]))

  (: exec-prim :
     Σ ℓ Symbol
     #:volatile? Boolean
     #:dom (-var V)
     #:rng W
     #:rng-wrap (Option (Listof V))
     #:refinements (Listof (List (Listof V) (Option V) (Listof V)))
     #:args W
     → (Values R (℘ Err)))
  (define (exec-prim
           Σ₀ ℓ o
           #:volatile? volatile?
           #:dom doms
           #:rng ranges
           #:rng-wrap ?range-wraps
           #:refinements refinements
           #:args args)
    (define l (ℓ-src ℓ))
    (define ℓ:o (loc->ℓ (loc o 0 0 '())))
    (define ctx* (Ctx l o ℓ:o ℓ))
    (define ctx (Ctx o l ℓ:o ℓ))
    (match-define (-var doms:init doms:rest) doms)

    (define (no-return?) (ormap (match-λ? {singleton-set (-● (singleton-set 'none/c))}) ranges))

    (define (simple-pred?)
      (and (null? refinements)
           (equal? 'boolean? (hash-ref range-table o #f))
           (not doms:rest)
           (andmap symbol? doms:init)))

    (define (args:behavioral? [args : W^])
      (define Vs*
        (for*/set: : V^ ([W (in-set args)]
                         [Vs (in-list W)]
                         [V (in-set Vs)] #:when (behavioral? V Σ₀))
          V))
      (and (not (set-empty? Vs*)) Vs*))

    (define (mk-rng [Σ : Σ])
      (define-values (Wₐ ΔΣ) (refine-ranges Σ refinements args ranges))
      (if ?range-wraps
          (with-pre ΔΣ (mon* (⧺ Σ ΔΣ) ctx (map {inst set V} ?range-wraps) Wₐ))
          (values (hash ΔΣ {set Wₐ}) ∅)))

    (with-collapsing/R [(ΔΣ₀ args*)
                        (if doms:rest
                            (let-values ([(args:init args:rest)
                                          (split-at args (length doms:init))])
                              (with-collapsing/R [(ΔΣ₀ args:init*)
                                                  (mon* Σ₀ ctx* (map (inst set V) doms:init) args:init)]
                                (with-collapsing/R [(ΔΣ₁ args:rest*)
                                                    (mon* (⧺ Σ₀ ΔΣ₀) ctx* (make-list (length args:rest) {set doms:rest}) args:rest)]
                                  (just (append (collapse-W^ args:init*) (collapse-W^ args:rest*)) (⧺ ΔΣ₀ ΔΣ₁)))))
                            (mon* Σ₀ ctx* (map (inst set V) doms:init) args))]
      (cond [(no-return?) (values ⊥R ∅)]
            [(simple-pred?) (with-pre ΔΣ₀ (implement-predicate (⧺ Σ₀ ΔΣ₀) o (collapse-W^ args*)))]
            [(args:behavioral? args*)
             =>
             (λ (Vs)
               (define Σ₁ (⧺ Σ₀ ΔΣ₀))
               (with-collapsing/R [(ΔΣ₁ _) (leak Σ₁ (γ:hv #f) Vs)]
                 (with-pre (⧺ ΔΣ₀ ΔΣ₁) (mk-rng (⧺ Σ₁ ΔΣ₁)))))]
            [else (with-pre ΔΣ₀ (mk-rng (⧺ Σ₀ ΔΣ₀)))])))

  (define alias-table : Alias-Table (make-alias-table #:phase 0))
  (define const-table : Parse-Prim-Table (make-parse-prim-table #:phase 0))
  (define prim-table  : (HashTable Symbol ⟦O⟧) (make-hasheq))
  (define opq-table   : (HashTable Symbol -●) (make-hasheq))
  (define debug-table : (HashTable Symbol Any) (make-hasheq))

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

  (: make-listof : V ℓ → V)
  (define (make-listof Cₕ ℓ)
    (define x (format-symbol "gen-listof-~a" ℓ))
    (γ:imm:listof x Cₕ ℓ))

  (: make-static-listof : Symbol (→ (Values V ℓ)) → V)
  (define make-static-listof
    (let ([cache : (Mutable-HashTable Symbol V) (make-hasheq)])
      (λ (tag mk-V)
        (hash-ref! cache tag (λ () (call-with-values mk-V make-listof))))))

  (: vec-len : V^ → V^)
  (define (vec-len V^)
    (match V^
      [{singleton-set (? T? T)} {set (T:@ 'vector-length (list T))}]
      [_
       (set-union-map
        (match-lambda
          [(Vect αs) {set (-b (length αs))}]
          [(Vect-Of _ αₙ) αₙ]
          [(Guarded _ (Vect/C αs _) _) {set (-b (length αs))}]
          [_ {set (-● {set 'exact-nonnegative-integer?})}])
        V^)]))

  (: refine-ranges : Σ (Listof (List (Listof V) (Option V) (Listof V))) W W → (Values W ΔΣ))
  (define (refine-ranges Σ cases args rng)

    (: obvious? : V V^ → Boolean)
    ;; Fast local check if `Vs` definitely satisfies `P`
    (define (obvious? P Vs)
      (define go : (V → ?Dec)
        (match-lambda
          [(Not/C (γ:imm P) _)
           (case (go P)
             [(✓) '✗]
             [(✗) '✓]
             [else #f])]
          [(? P? P) (sat Σ P Vs)]
          [_ #f]))
      (eq? (go P) '✓))

    ;; For each refinement case, if args satisfy domain, refine result with range
    (for/fold ([rng* : W rng] [ΔΣ* : ΔΣ ⊥ΔΣ]) ([kase (in-list cases)])
      (match-define (list dom-inits ?dom-rst refinements) kase)

      (: check-inits : (Listof V) W → (Values W ΔΣ))
      (define check-inits
        (match-lambda**
         [((cons dom doms*) (cons arg args*))
          (if (obvious? dom arg) (check-inits doms* args*) (values rng* ΔΣ*))]
         [('() args) (check-rest args)]
         [((cons _ _) '()) (values rng* ΔΣ*)]))

      (: check-rest : W → (Values W ΔΣ))
      (define (check-rest args)
        (cond [?dom-rst
               (let go ([args : W args])
                 (match args
                   ['() (refine-rng)]
                   [(cons arg args*) (if (obvious? ?dom-rst arg)
                                         (go args*)
                                         (values rng* ΔΣ*))]))]
              [else (if (null? args) (refine-rng) (values rng* ΔΣ*))]))

      (define (refine-rng) : (Values W ΔΣ)
        (define-values (rng-rev ΔΣ**)
          (for/fold ([rng-rev : W '()] [ΔΣ* : ΔΣ ΔΣ*])
                    ([rngᵢ (in-list rng*)] [refᵢ (in-list refinements)])
            (define-values (rngᵢ* ΔΣᵢ) (refine rngᵢ refᵢ Σ))
            (values (cons rngᵢ* rng-rev) (⧺ ΔΣ* ΔΣᵢ))))
        (values (reverse rng-rev) ΔΣ**))

      (check-inits dom-inits args)))

  ;; Eta-expand to get aroudn undefined and init-depend
  (: r:err : (U (℘ Err) Err) → (Values R (℘ Err)))
  (define (r:err e) (err e))
  (: r:just : ([(U V V^ W)] [ΔΣ] . ->* . (Values R (℘ Err))))
  (define (r:just V [ΔΣ ⊥ΔΣ]) (just V ΔΣ))
  (: r:blm : (-l ℓ ℓ W W → (℘ Blm)))
  (define (r:blm l+ ℓ ℓₒ ctc val) (blm l+ ℓ ℓₒ ctc val))
  (: r:reify : (℘ P) → V^)
  (define (r:reify Cs) (reify Cs))
  (: r:with-split-Σ : (Σ P W (W ΔΣ → (Values R (℘ Err))) (W ΔΣ → (Values R (℘ Err)))
                         → (Values R (℘ Err))))
  (define (r:with-split-Σ Σ P W on-t on-f) (with-split-Σ Σ P W on-t on-f))
  (: r:⧺ : ΔΣ ΔΣ * → ΔΣ)
  (define (r:⧺ ΔΣ₀ . ΔΣs) (apply ⧺ ΔΣ₀ ΔΣs))
  (: r:ΔΣ⧺R : ΔΣ R → R)
  (define (r:ΔΣ⧺R ΔΣ R) (ΔΣ⧺R ΔΣ R))
  )
