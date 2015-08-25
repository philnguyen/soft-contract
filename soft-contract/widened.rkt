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

(: Cfg-final? : -Cfg -Ξ → Boolean)
(define (Cfg-final? C Ξ)
  (match-define (-Cfg E _ τ) C)
  (final? E τ Ξ))

(: ↦/ξ : -ξ → (Option -ξ))
;; Reduction relation on widened state
(define (↦/ξ ξ)
  ;; FIXME: do this the efficient way
  (match-define (-ξ Cs σ Ξ M) ξ)
  (define ςs
    (for/fold ([ςs : (Setof -ς) ∅])
              ([C Cs] #:unless (Cfg-final? C Ξ))
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

(: dbg/ξ : Path-String → (Values (Integer → -ξ) (Integer Integer → -ξ) (Setof -Cfg)))
(define (dbg/ξ p)
  (define ξ₀ (𝑰/ξ (files->prog (list p))))
  
  (define-values (ξ evals)
    (let go : (Values -ξ (Map Integer -ξ))
         ([ξ ξ₀] [i 1] [evals : (Map Integer -ξ) (hash 0 ξ₀)])
      (define ξ* (↦/ξ ξ))
      (cond
        [ξ* (go ξ* (+ i 1) (hash-set evals i ξ*))]
        [else (values ξ evals)])))
  
  (define (step [n : Integer]) : -ξ
    (hash-ref evals n (λ () (error 'dbg/ξ "undefined for ~a" (hash-count evals)))))
  
  (define (diff [n₀ : Integer] [n₁ : Integer]) : -ξ
    (ξ-subtract (step n₁) (step n₀)))

  (define answers
    (let ()
      (match-define (-ξ Cs* _ Ξ* _) (hash-ref evals (- (hash-count evals) 1)))

      (for*/set: : (Setof -Cfg) ([C Cs*] #:when (Cfg-final? C Ξ*))
        C)))
  
  (values step diff answers))

(define-values (f s ans) (dbg/ξ "test/programs/safe/1.rkt"))
