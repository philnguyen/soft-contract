#lang typed/racket/base
(require
 racket/match racket/set racket/list racket/bool racket/function
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt" "delta.rkt" "machine.rkt" "reduction.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)])

;; configuration
(struct -Cfg ([e : -E] [Γ : -Γ] [τ : -τ]) #:transparent)
;; state with widened stores and summarization
(struct -ξ ([cs : (Setof -Cfg)] [σ : -σ] [Ξ : -Ξ] [M : -M]) #:transparent)

(: 𝑰/ξ : -prog → -ξ)
;; Load initial widened state
(define (𝑰/ξ p)
  (match-define (-ς E Γ τ σ Ξ M) (𝑰 p))
  (-ξ {set (-Cfg E Γ τ)} σ Ξ M))

(: ↦/ξ : -ξ → (Option -ξ))
;; Reduction relation on widened state
(define (↦/ξ ξ)
  ;; FIXME: do this the efficient way
  (match-define (-ξ Cs σ Ξ M) ξ)
  (define ςs
    (for/fold ([ςs : (Setof -ς) ∅]) ([C Cs])
      (match-define (-Cfg E Γ τ) C)
      (match (↦ (-ς E Γ τ σ Ξ M))
        [(? -ς? ς) (set-add ςs ς)]
        [(? set? s) (set-union ςs s)])))
  (define-values (Cs* σ* Ξ* M*)
    (for/fold ([Cs* : (Setof -Cfg) Cs] [σ* : -σ σ] [Ξ* : -Ξ Ξ] [M* : -M M])
              ([ςi ςs])
      (match-define (-ς Ei Γi τi σi Ξi Mi) ςi)
      (values (set-add Cs* (-Cfg Ei Γi τi))
              (⊔/m σ* σi)
              (⊔/m Ξ* Ξi)
              (⊔/m M* Mi))))
  (cond
    [(and (equal? Cs* Cs) (equal? σ* σ) (equal? Ξ* Ξ) (equal? M* M)) #f]
    [else (-ξ Cs* σ* Ξ* M*)]))


;;;;; For testing only

(: ξ-subtract : -ξ -ξ → -ξ)
;; Compute new stuff in `ξ₁` not in `ξ₀`
(define (ξ-subtract ξ₁ ξ₀)
  (match-define (-ξ Cs₀ σ₀ Ξ₀ M₀) ξ₀)
  (match-define (-ξ Cs₁ σ₁ Ξ₁ M₁) ξ₁)
  (-ξ (set-subtract Cs₁ Cs₀)
      (mmap-subtract σ₁ σ₀)
      (mmap-subtract Ξ₁ Ξ₀)
      (mmap-subtract M₁ M₀)))

(: dbg/ξ : Path-String → (Values (Integer → -ξ) (Integer Integer → -ξ)))
(define (dbg/ξ p)
  (define ξ₀ (𝑰/ξ (files->prog (list p))))
  (define (step [n : Integer]) : -ξ
    (for/fold ([ξ ξ₀]) ([i (in-range n)])
      (or (↦/ξ ξ)
          (error 'dbg/ξ "undefined for ~a~n" i))))
  (define (diff [n₀ : Integer] [n₁ : Integer]) : -ξ
    (ξ-subtract (step n₁) (step n₀)))
  (values step diff))

(define-values (f s) (dbg/ξ "test/programs/safe/1.rkt"))
