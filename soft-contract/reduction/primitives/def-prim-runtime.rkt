#lang typed/racket/base

;; This module provides runtime support for the def-prim DSL

(provide (all-defined-out))
(require racket/match
         racket/set
         "../../utils/set.rkt"
         "../../utils/map.rkt"
         "../../utils/function.rkt"
         "../../utils/pretty.rkt"
         "../../utils/def.rkt"
         "../../utils/list.rkt"
         "../../ast/definition.rkt"
         "../../runtime/main.rkt"
         "../../proof-relation/main.rkt")

(define-type -⟦o⟧! (-⟪ℋ⟫ -ℓ -l -Σ -Γ (Listof -W¹) → (℘ -ΓA)))
(define-type Prim-Thunk (-Γ → (℘ -ΓA)))

(: unchecked-ac : -σ -st-ac -W¹ → (℘ -W¹))
;; unchecked struct accessor, assuming the value is already checked to be the right struct.
;; This is only for use internally, so it's safe (though imprecise) to ignore field wraps
(define (unchecked-ac σ ac W)
  (define-set seen : -⟪α⟫ #:eq? #t #:as-mutable-hash? #t)
  (match-define (-W¹ (list V) s) W)
  (match-define (-st-ac 𝒾 i) ac)
  (define s* (-?@ ac s))
  (let go ([V : -V V])
    (match V
      [(-St (== 𝒾) αs)
       (for/set: : (℘ -W¹) ([V* (in-set (σ@ σ (list-ref αs i)))])
         (-W¹ V* s*))]
      [(-St* (== 𝒾) _ α _)
       (cond [(seen-has? α) ∅]
             [else
              (seen-add! α)
              (for/union : (℘ -W¹) ([V (in-set (σ@ σ α))]) (go V))])]
      [(? -●?) {set (-W¹ -●/V s*)}]
      [_ ∅])))

(: ⊢?/quick : -R -σ -Γ -o -W¹ * → Boolean)
;; Perform a relatively cheap check (i.e. no SMT call) if `(o W ...)` returns `R`
(define (⊢?/quick R σ Γ o . Ws)
  (define-values (Vs ss) (unzip-by -W¹-V -W¹-s Ws))
  (eq? R (first-R (apply p∋Vs σ o Vs)
                  (Γ⊢e Γ (apply -?@ o ss)))))

(: blm : -Γ -l -l (U -V -v) -W¹ → (℘ -ΓA))
(define (blm Γ who whom why what)
  {set (-ΓA Γ (-blm who whom (list why) (list (-W¹-V what))))})

(: implement-predicate : -M -σ -Γ Symbol (Listof -W¹) → (℘ -ΓA))
(define (implement-predicate M σ Γ o Ws)
  (define ss (map -W¹-s Ws))
  (define A
    (case (apply MΓ⊢oW M σ Γ 'o Ws)
      [(✓) -True/Vs]
      [(✗) -False/Vs]
      [(?) -Bool/Vs]))
  {set (-ΓA Γ (-W A (apply -?@ o ss)))})

(define/memoeq (total-pred [n : Index]) : (Symbol → -⟦o⟧!)
  (define cs (list (format-symbol "~a values" n)))
  (λ (o)
    (λ (⟪ℋ⟫ ℓ l Σ Γ Ws)
      (cond [(equal? n (length Ws))
             (match-define (-Σ σ _ M) Σ)
             (implement-predicate M σ Γ o Ws)]
            [else
             {set (-ΓA Γ (-blm l o cs (map -W¹-V Ws)))}]))))

(define alias-table : (HashTable Symbol -o) (make-hasheq))
(define const-table : (HashTable Symbol -b) (make-hasheq))
(define prim-table  : (HashTable Symbol -⟦o⟧!) (make-hasheq))
(define opq-table   : (HashTable Symbol -●) (make-hasheq))
(define debug-table : (HashTable Symbol Any) (make-hasheq))
(define implication-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
(define exclusion-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
(define implication-table⁻¹ : (HashTable Symbol (℘ Symbol)) (make-hasheq))

(: get-prim : Symbol → (Option (U -o -b -●)))
(define (get-prim name)
  (cond [(hash-has-key? prim-table name) name]
        [(hash-ref const-table name #f) => values]
        [(hash-ref alias-table name #f) => values]
        [(hash-ref opq-table name #f) => values]
        [else #f]))

(: add-implication! : Symbol Symbol → Void)
;; Extend implication table and take care of transitivity
(define (add-implication! p q)
  (unless (map-has? implication-table p q #:eq? #t)
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
  (unless (map-has? exclusion-table p q #:eq? #t)
    (map-add! exclusion-table p q)
    ;; (p → ¬q) and (q₀ → q) implies (p → ¬q₀)
    (for ([q₀ (in-set (get-strongers q))])
      (add-exclusion! p q₀))
    (for ([p₀ (in-set (get-strongers p))])
      (add-exclusion! p₀ q))
    ;; exclusion is symmetric
    (add-exclusion! q p)))

(:* get-weakers get-strongers get-exclusions : Symbol → (℘ Symbol))
(define (get-weakers    p) (hash-ref implication-table   p →∅eq))
(define (get-strongers  p) (hash-ref implication-table⁻¹ p →∅eq))
(define (get-exclusions p) (hash-ref exclusion-table     p →∅eq))
