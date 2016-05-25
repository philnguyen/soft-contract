#lang typed/racket/base

;; This module provides abbreviations and extra tools for dealing with sets
(provide
 ℘ ∅ ∅eq ∪ ∩ →∅ ∋ ∈ ⊆ --
 set-add-list define-set set-partition for/union collect merge set->predicate map/set)

(require
 racket/match racket/set
 (for-syntax racket/base racket/syntax))

(define-type ℘ Setof)
(define ∅ : (℘ Nothing) (set))
(define ∅eq : (℘ Nothing) (seteq))
(define ∪ set-union)
(define ∩ set-intersect)
(define →∅ : (→ (℘ Nothing)) (λ () ∅))
(define ∋ set-member?)
(define #:∀ (X) (∈ [x : X] [xs : (℘ X)]) : Boolean (∋ xs x))
(define ⊆ subset?)
(define -- set-subtract)

(: set-add-list : (∀ (A) (℘ A) (Listof A) → (℘ A)))
;; Add each element in given list to set
(define (set-add-list xs x-list)
  (for/fold ([xs* : (℘ A) xs]) ([x x-list])
    (set-add xs* x)))

;; Define set with shortened syntax for (imperative) adding and membership testing
(define-syntax (define-set stx)
  (syntax-case stx (:)
    [(_ s : τ)
     (with-syntax ([s-has? (format-id #'s "~a-has?" #'s)]
                   [s-add! (format-id #'s "~a-add!" #'s)]
                   [s-add*! (format-id #'s "~a-add*!" #'s)]
                   [s-union! (format-id #'s "~a-union!" #'s)])
       #'(begin (define s : (℘ τ) ∅)
                (define (s-has? [x : τ]) : Boolean (∋ s x))
                (define (s-add! [x : τ]) (set! s (set-add s x)))
                (define (s-add*! [xs : (Listof τ)]) (set! s (∪ s (list->set xs))))
                (define (s-union! [xs : (℘ τ)]) (set! s (∪ s xs)))))]))

(: set-partition (∀ (X) (X → Boolean) (℘ X) → (Values (℘ X) (℘ X))))
;; Partition set members into those that satisfy the predicate and the rest
(define (set-partition p xs)
  (for/fold ([pass : (℘ X) ∅] [fail : (℘ X) ∅]) ([x xs])
    (if (p x)
        (values (set-add pass x) fail)
        (values pass (set-add fail x)))))

(define-syntax for/union
  (syntax-rules (:)
    [(_ : τ (for-clauses ...) body ...)
     (for/fold ([acc : τ ∅]) (for-clauses ...)
       (set-union acc (let () body ...)))]
    [(_ (for-clauses ...) body ...)
     (for/fold ([acc ∅]) (for-clauses ...)
       (set-union acc (let () body ...)))]))

;(: collect (∀ (X) (Option X) * → (U X (℘ X))))
;; Collect all non-#f value into set,
;; optionally unpack set of size 1
(define-syntax collect
  (syntax-rules ()
    [(_) ∅]
    [(_ x z ...)
     (let ([x* x]
           [z* (collect z ...)])
       (cond [(set? x*)
              (cond [(set? z*) (∪ x* z*)]
                    [else (set-add x* z*)])]
             [x*
              (cond [(set? z*) (if (set-empty? z*) x* (set-add z* x*))]
                    [else {set z* x*}])]
             [else z*]))]))

;(: merge (∀ (X) (U X (℘ X)) * → (U X (℘ X))))
(define-syntax merge
  (syntax-rules ()
    [(_) ∅]
    [(_ x) x]
    [(_ x xs ...)
     (let ([xs↓ (merge xs ...)]
           [x↓ x])
       (cond [(set? xs↓) (if (set? x↓) (∪ x↓ xs↓) (set-add xs↓ x↓))]
             [else (if (set? x↓) (set-add x↓ xs↓) {set x↓ xs↓})]))]))

(: set->predicate (∀ (X) (℘ X) → (X → Boolean)))
;; Convert set to predicate
(define ((set->predicate xs) x) (∋ xs x))

(: map/set (∀ (X Y) (X → Y) (℘ X) → (℘ Y)))
;; Like `map`, but for set
(define (map/set f xs)
  (for/set: : (℘ Y) ([x : X xs]) (f x)))
