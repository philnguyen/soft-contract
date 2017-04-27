#lang typed/racket/base

;; This module defines facilities for asserting and querying assumptions
;; about primitive operations, namely:
;; - implications and exclusions between primitive predicates
;; - (conservative) ranges of primitive operations
;; - arities of primitive operations

(require racket/match
         racket/set
         set-extras
         "../utils/def.rkt"
         "../utils/map.rkt"
         "../utils/debug.rkt"
         "../ast/arity.rkt"
         "../runtime/verification-result.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Implication and Exclusion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide add-implication! add-exclusion!
         get-weakers get-strongers get-exclusions o⇒o)

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

(: o⇒o : Symbol Symbol → -R)
(define (o⇒o p q)
  (cond [(eq? p q) '✓]
        [(∋ (get-weakers p) q) '✓]
        [(∋ (get-exclusions p) q) '✗]
        [else '?]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Range
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide set-range! get-conservative-range
         set-partial! partial-prims)

(define range-table : (HashTable Symbol Symbol) (make-hasheq))
(define partial-prims : (HashTable Symbol Natural) (make-hasheq))

(: set-range! : Symbol Symbol → Void)
(define (set-range! o r) (hash-set-once! range-table o r))

(: set-partial! : Symbol Natural → Void)
(define (set-partial! o n) (hash-set! partial-prims o n))

(: get-conservative-range : Symbol → Symbol)
(define (get-conservative-range o) (hash-ref range-table o (λ () 'any/c)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Arity
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide update-arity! get-arity V-arity formals-arity guard-arity)

(define arity-table : (HashTable Symbol Arity) (make-hasheq))

(: update-arity! : Symbol Arity → Void)
(define (update-arity! o a)
  (cond [(hash-ref arity-table o #f) =>
         (λ ([a₀ : Arity])
           (unless (arity-includes? a₀ a)
             (hash-set! arity-table o (normalize-arity (list a₀ a)))))]
        [else
         (hash-set! arity-table o a)]))

(: get-arity : Symbol → Arity)
(define (get-arity o) (hash-ref arity-table o (λ () (error 'get-arity "nothing for ~a" o))))

;;;;; TODO stuff below migrated from `runtime` to here
;;;;; not the most appropriate place...

(require (only-in racket/list remove-duplicates)
         "../ast/definition.rkt"
         "../ast/static-info.rkt"
         "../runtime/definition.rkt")

(define formals-arity : (-formals → Arity)
  (match-lambda
    [(-var init _) (arity-at-least (length init))]
    [(? list? xs) (length xs)]))

(define guard-arity : (-=>_ → Arity)
  (match-lambda
    [(-=> αs _ _) (shape αs)]
    [(and grd (-=>i αs (list mk-D mk-d _) _))
     (match mk-D
       [(-Clo xs _ _ _) (formals-arity xs)]
       [_
        ;; FIXME: may be wrong for var-args. Need to have saved more
        (length αs)])]))

(: V-arity : -V → (Option Arity))
;; Return given value's arity, or `#f` if it's not a procedure
(define V-arity
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
