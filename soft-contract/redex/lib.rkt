#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics racket/contract racket/set racket/list rackunit)

(define/contract ((map/c k? v?) x)
  ((any/c . -> . any) (any/c . -> . any) . -> . (any/c . -> . any))
  (and (hash? x)
       (for/and ([(k v) (in-hash x)])
         (and (k? k) (v? v)))))

(define/contract (mmap/c k? v?)
  ((any/c . -> . any) (any/c . -> . any) . -> . (any/c . -> . any))
  (map/c k? (set/c v?)))

(define/contract (check-same-set? s t)
  ((listof any/c) (listof any/c) . -> . any)
  (check-equal? (list->set s) (list->set t)))

(define/contract (mmap-diff h₁ h₂)
  ((mmap/c any/c any/c) (mmap/c any/c any/c) . -> . (mmap/c any/c any/c))
  (for/fold ([acc (hash)]) ([(k v) (in-hash h₁)])
    (define diff (set-subtract v (hash-ref h₂ k set)))
    (cond [(set-empty? diff) acc]
          [else (hash-set acc k diff)])))

(define-language redex
  ;; Generics
  [S (side-condition (name S any) (set? (term S)))] ; set of something
  [M1 (side-condition (name M1 any) (hash? (term M1)))] ; map
  [MM (side-condition (name MM any) ((map/c any/c set?) (term MM)))] ; map whose range is set
  )

(define-metafunction redex
  M+ : [any ↦ any] ... -> M1
  [(M+ [any_k ↦ any_v] ...)
   ,(for/hash ([k (term (any_k ...))] [v (term (any_v ...))])
      (values k v))])

(define-metafunction redex
  ++ : M1 [any ↦ any] ... -> M1
  [(++ M1 [any_k ↦ any_v] ...)
   ,(for/fold ([M (term M1)]) ([k (term (any_k ...))] [v (term (any_v ...))])
      (hash-set M k v))])

(define-metafunction redex
  MM⊔ : MM [any ↦ any] ... -> MM
  [(MM⊔ MM [any_k ↦ any_v] ...)
   ,(for/fold ([m (term MM)]) ([k (in-list (term (any_k ...)))]
                               [v (in-list (term (any_v ...)))])
      (hash-update m k (λ (vs) (set-add vs v)) set))])

(define-metafunction redex
  ⊔ : MM MM -> MM
  [(⊔ MM_1 MM_2)
   ,(for/fold ([MM (term MM_1)]) ([(k vs) (in-hash (term MM_2))])
      (hash-update MM k (λ (vs*) (set-union vs* vs)) set))])

(define-metafunction redex
  lookup : M1 any -> any
  [(lookup M1 any) ,(hash-ref (term M1) (term any))])

(define-metafunction redex
  dom : M1 -> any
  [(dom M1) ,(list->set (hash-keys (term M1)))])

(define-metafunction redex
  S+ : any ... -> S
  [(S+ any ...) ,(list->set (term (any ...)))])

(define-judgment-form redex
  #:contract (∈ any S)
  #:mode     (∈ O   I)
  [(where {_ ... any _ ...} ,(set->list (term S)))
   ----------------------------------------------- "non-det"
   (∈ any S)])

(define-judgment-form redex
  #:contract (set-split S S any)
  #:mode     (set-split I O O  )
  [(where {any_1 ... any any_2 ...} ,(set->list (term S)))
   (where S_1 ,(list->set (term (any_1 ... any_2 ...))))
   ----------------------------------------------- "non-det"
   (set-split S S_1 any)])

(define-metafunction redex
  ∪ : S ... -> S
  [(∪ S ...)
   ,(for/fold ([s {set}]) ([Si (term (S ...))])
      (set-union s Si))])

(define-metafunction redex
  -- : S S -> S
  [(-- S_1 S_2) ,(set-subtract (term S_1) (term S_2))])

(define-term ∅ ,(set))
(define-term ⊥ ,(hash))

(module+ test
  (test-equal (term (∪ {S+ 1 3 5} {S+ 3 4 5}))
              (term {S+ 1 3 4 5}))
  (test-equal (term (-- {S+ 1 2 3 4 5} {S+ 2 4}))
              (term {S+ 1 3 5}))
  (define-term MM₁ (MM⊔ ⊥ [1 ↦ 2] [3 ↦ 4] [1 ↦ 3]))
  (test-equal (term (dom MM₁)) (term {S+ 1 3}))
  (test-equal (term (lookup MM₁ 1)) (term {S+ 2 3}))
  )
