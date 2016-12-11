#lang typed/racket/base

(provide run-file havoc-file run-e)

(require "utils/main.rkt"
         "ast/main.rkt"
         "runtime/definition.rkt"
         "parse/main.rkt"
         "reduction/compile/main.rkt"
         "reduction/init.rkt"
         "reduction/quick-step.rkt")

(: run-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (run-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define-values (σ₁ _) (𝑰 (list m)))
    (run (↓ₘ m) σ₁)))

(: havoc-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (havoc-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define-values (σ₁ e₁) (𝑰 (list m)))
    (run (↓ₚ (list m) e₁) σ₁)))

(: run-e : -e → (Values (℘ -ΓA) -Σ))
(define (run-e e)
  (with-initialized-static-info
    (define-values (σ₀ _) (𝑰 '()))
    (run (↓ₑ 'top e) σ₀)))

(module+ test
  (require "utils/main.rkt")
  ((inst profile-thunk Void)
   (λ ()
     (printf "profiling execution of `slatex`~n")
     (havoc-file "../test/programs/safe/big/slatex.rkt")
     (void))))
