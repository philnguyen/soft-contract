#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics racket/set racket/contract racket/list)

(define-language empty-lang)

;; extend environment
(define-metafunction empty-lang
  ++ : {[any any any] ...} [any any any] ... -> {[any any any] ...}
  [(++ any) any]
  [(++ any any_1 any_i ...) (++ (++₁ any any_1) any_i ...)])
(define-metafunction empty-lang
  ++₁ : {[any any any] ...} [any any any] -> {[any any any] ...}
  [(++₁ {any_1 ... [any_k any_↦ _] any_2 ...} [any_k any_↦ any_v])
   {any_1 ... [any_k any_↦ any_v] any_2 ...}]
  [(++₁ {any ...} [any_k any_↦ any_v]) {any ... [any_k any_↦ any_v]}])

;; update environment
(define-metafunction empty-lang
  !! : {[any any any] ...} [any any any] -> {[any any any] ...}
  [(!! {any_1 ... [any_k any_↦ _] any_2 ...} [any_k any_↦ any_v])
   {any_1 ... [any_k any_↦ any_v] any_2 ...}])

;; look up environment
(define-metafunction empty-lang
  @ : {[any _ any] ...} any -> any
  [(@ {_ ... [any_k _ any_v] _ ...} any_k) any_v])

;; return environment's domain
(define-metafunction empty-lang
  dom : {(any _ any) ...} -> {any ...}
  [(dom {[any_x _ _] ...}) {any_x ...}])

(define-relation empty-lang
  ∈ ⊆ any × {any ...}
  [(∈ any {_ ... any _ ...})])

(define-relation empty-lang
  ∉ ⊆ any × {any ...}
  [(∉ any any_s) (where #f (∈ any any_s))])

(define-metafunction empty-lang
  ⊆ : {any ...} {any ...} -> boolean
  [(⊆ any_1 any_2) ,(subset? (list->set (term any_1)) (list->set (term any_2)))])

(define-metafunction empty-lang
  ∩ : {any ...} {any ...} ... -> {any ...}
  [(∩ any_1 any_2 ...)
   ,(set->list (apply set-intersect (list->set (term any_1)) (map list->set (term (any_2 ...)))))])

(define-metafunction empty-lang
  -- : {any ...} {any ...} -> {any ...}
  [(-- any_1 any_2)
   ,(set->list (set-subtract (list->set (term any_1)) (list->set (term any_2))))])

(define-metafunction empty-lang
  ¬ : any -> boolean
  [(¬ #f) #t]
  [(¬ _) #f])

(define-metafunction empty-lang
  ∪ : {any ...} ... -> {any ...}
  [(∪ any ...) ,(set->list (apply set-union {set} (map list->set (term (any ...)))))])

(define/contract (cap n xs)
  (integer? (listof any/c) . -> . (listof any/c))
  (take xs (min n (length xs))))

