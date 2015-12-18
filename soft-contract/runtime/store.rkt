#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set racket/list
 "../utils/map.rkt" "../utils/untyped-macros.rkt" "../ast/definition.rkt"
 "path-inv.rkt" "addr.rkt" "val.rkt" "env.rkt")

;; store maps addresses to values
(define-type -σ (MMap -α -V))
(define -σ⊥ : -σ (hash))
(define-type -Δσ (ΔMap -α -V))

(: σ@ : -σ -α → (Setof -V))
;; Look up the store for all values at given address
(define (σ@ σ α) (hash-ref σ α))

(: σ@₁ : -σ -α → -V)
;; Look up the store for a single value at given address
(define (σ@₁ σ α)
  (define Vs (hash-ref σ α))
  (cond
    [(= 1 (set-count Vs)) (set-first Vs)]
    [else (error 'Internal "expect exactly 1 value at address ~a, given ~a"
                 α (set-count Vs))]))

(: σ@/list : -σ (Listof -α) → (Setof (Listof -V)))
;; Look up store, return every possible list of values
(define (σ@/list σ αs)
  (match αs
    ['() {set (list)}]
    [(cons α βs)
     (define Vss (σ@/list σ βs))
     (for*/set: : (Setof (Listof -V)) ([V (σ@ σ α)] [Vs Vss])
       (cons V Vs))]))

(define (show-σ [σ : -σ]) : (Listof Sexp)
  (for/list ([(α Vs) (in-hash σ)])
    `(,(show-α α) ↦ ,@(for/list : (Listof Sexp) ([V Vs]) (show-V V)))))

(: alloc-varargs : -Γ (Listof -V) Integer → (Values -Δσ -V))
;; Given list of value, allocate it in store for varargs,
;; returning the store different and the arg list
(define (alloc-varargs Γ Vs pos)
  (let go ([Vs : (Listof -V) Vs] [i : Integer (- (length Vs) 1)])
    (match Vs
      ['() (values '() -Null)]
      [(cons V Vs*)
       (define-values (δσ V-rest) (go Vs* (- i 1)))
       (define i* (assert i exact-nonnegative-integer?))
       (define α-car (-α.var-car pos i*))
       (define α-cdr (-α.var-cdr pos i*))
       (values (list* (cons α-car (close-Γ Γ V))
                      (cons α-cdr V-rest)
                      δσ)
               (-St -s-cons (list α-car α-cdr)))])))

(: unalloc-varargs : -σ -V → (Setof (Listof -V)))
;; Given an allocated value list, extract the value list
(define (unalloc-varargs σ V)
  (match V
    [(-b '()) {set '()}]
    [(-St (≡ -s-cons) (list α₁ α₂))
     (for*/set: : (Setof (Listof -V)) ([V₁ (σ@ σ α₁)]
                                       [V₂ (σ@ σ α₂)]
                                       [Vs (unalloc-varargs σ V₂)])
       (cons V₁ Vs))]))

(: alloc : -Γ -ρ -formals (Listof -V) Integer → (Values -Δσ -ρ))
(define (alloc Γ ρ xs Vs pos)

  (: alloc-list : -ρ (Listof Symbol) (Listof -V) → (Values -Δσ -ρ))
  (define (alloc-list ρ xs Vs)
    (for/fold ([δσ : -Δσ '()] [ρ : -ρ ρ]) ([x xs] [V Vs])
      (define α (-α.x x Γ))
      (values (cons (cons α (close-Γ Γ V)) δσ)
              (ρ+ ρ x α))))

  (match xs
    [(-varargs xs-init x-rest)
     (define-values (Vs-init Vs-rest) (split-at Vs (length xs-init)))
     (define-values (δσ₀ ρ₀) (alloc-list ρ xs-init Vs-init))
     (define-values (δσ₁ V-rest) (alloc-varargs Γ Vs-rest pos))
     (define α-rest (-α.x x-rest Γ))
     (values `(,(cons α-rest V-rest) ,@δσ₀ ,@δσ₁)
             (ρ+ ρ₀ x-rest α-rest))]
    [(? list? xs) (alloc-list ρ xs Vs)]))
