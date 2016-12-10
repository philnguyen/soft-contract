#lang typed/racket/base

;; This module defines facilities for declaring implications and exclusions
;; between primitive predicates

(provide add-implication! add-exclusion!
         get-weakers get-strongers get-exclusions o⇒o)

(require racket/set
         "../../utils/def.rkt"
         "../../utils/set.rkt"
         "../../utils/map.rkt"
         "result.rkt")

(define implication-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
(define exclusion-table : (HashTable Symbol (℘ Symbol)) (make-hasheq))
(define implication-table⁻¹ : (HashTable Symbol (℘ Symbol)) (make-hasheq))

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

(: o⇒o : Symbol Symbol → -R)
(define (o⇒o p q)
  (cond [(∋ (get-weakers p) q) '✓]
        [(∋ (get-exclusions p) q) '✗]
        [else '?]))
