#lang typed/racket/base

;; This module defines facilities for asserting and querying assumptions
;; about primitive operations, namely:
;; - implications and exclusions between primitive predicates
;; - (conservative) ranges of primitive operations
;; - arities of primitive operations

(require racket/match
         racket/set
         (only-in racket/list remove-duplicates)
         typed/racket/unit
         set-extras
         "../utils/def.rkt"
         "../utils/map.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "signatures.rkt")

(provide local-prover-base@)

(define-unit local-prover-base@
  (import)
  (export local-prover-base^)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Implication and Exclusion
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define implication-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
  (define exclusion-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
  (define implication-table⁻¹ : (HashTable Symbol (℘ Symbol)) (make-hasheq))

  ;; Extend implication table and take care of transitivity
  (define (add-implication! [p : Symbol] [q : Symbol]) : Void
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

  ;; Extend exclusion table and take care of inferring existing implication
  (define (add-exclusion! [p : Symbol] [q : Symbol]) : Void
    (unless (map-has? exclusion-table p q)
      (map-add! exclusion-table p q #:eq? #t)
      ;; (p → ¬q) and (q₀ → q) implies (p → ¬q₀)
      (for ([q₀ (in-set (get-strongers q))])
        (add-exclusion! p q₀))
      (for ([p₀ (in-set (get-strongers p))])
        (add-exclusion! p₀ q))
      ;; exclusion is symmetric
      (add-exclusion! q p)))

  (define (get-weakers    [p : Symbol]) (hash-ref implication-table   p mk-∅eq))
  (define (get-strongers  [p : Symbol]) (hash-ref implication-table⁻¹ p mk-∅eq))
  (define (get-exclusions [p : Symbol]) (hash-ref exclusion-table     p mk-∅eq))

  (define (o⇒o [p : Symbol] [q : Symbol])
    (cond [(eq? p q) '✓]
          [(∋ (get-weakers p) q) '✓]
          [(∋ (get-exclusions p) q) '✗]
          [else '?]))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Range
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define range-table : (HashTable Symbol Symbol) (make-hasheq))
  (define partial-prims : (HashTable Symbol Natural) (make-hasheq))

  (define (set-range! [o : Symbol] [r : Symbol]) (hash-set-once! range-table o r))
  (define (set-partial! [o : Symbol] [n : Natural]) (hash-set! partial-prims o n))
  (define (get-conservative-range [o : Symbol]) (hash-ref range-table o (λ () 'any/c)))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Arity
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define arity-table : (HashTable Symbol Arity) (make-hasheq))

  (define (update-arity! [o : Symbol] [a : Arity])
    (cond [(hash-ref arity-table o #f) =>
           (λ ([a₀ : Arity])
             (unless (arity-includes? a₀ a)
               (hash-set! arity-table o (normalize-arity (list a₀ a)))))]
          [else
           (hash-set! arity-table o a)]))

  (define (get-arity [o : Symbol])
    (hash-ref arity-table o (λ () (error 'get-arity "nothing for ~a" o))))

  ;;;;; TODO stuff below migrated from `runtime` to here
  ;;;;; not the most appropriate place...

  ;; Return given value's arity, or `#f` if it's not a procedure
  (define V-arity : (-V → (Option Arity))
    (match-lambda
      [(-Clo xs _ _ _) (formals-arity xs)]
      [(-Case-Clo clauses _ _)
       (remove-duplicates
        (for/list : (Listof Natural) ([clause clauses])
          (match-define (cons xs _) clause)
          (length xs)))]
      [(or (-And/C #t _ _) (-Or/C #t _ _) (? -Not/C?) (-St/C #t _ _) (? -One-Of/C?)) 1]
      [(-Ar guard _ _) (guard-arity guard)]
      [(? -st-p?) 1]
      [(-st-mk 𝒾) (get-struct-arity 𝒾)]
      [(? -st-ac?) 1]
      [(? -st-mut?) 2]
      [(? symbol? o) (hash-ref arity-table o)]
      [(-● _) #f]
      [V
       (printf "Warning: call `V-arity` on an obviously non-procedure ~a" (show-V V))
       #f]))
  )

