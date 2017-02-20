#lang typed/racket/base

(provide run-file havoc-file run-e)

(require racket/match
         "utils/main.rkt"
         "ast/main.rkt"
         "runtime/definition.rkt"
         "parse/main.rkt"
         "reduction/compile/main.rkt"
         "reduction/quick-step.rkt"
         "reduction/havoc.rkt")

(: run-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (run-file p)
  (with-initialized-static-info
    (run (↓ₘ (file->module p)))))

(: havoc-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (havoc-file p)
  (with-initialized-static-info
    (define m (file->module p))
    (define e (gen-havoc-expr (list m)))
    (run (↓ₚ (list m) e))))

(: run-e : -e → (Values (℘ -ΓA) -Σ))
(define (run-e e)
  (with-initialized-static-info
    (run (↓ₑ 'top e))))

(module+ test
  (require "utils/main.rkt")
  ((inst profile-thunk Void)
   (λ ()
     (printf "profiling execution of `slatex`~n")
     (havoc-file "../test/programs/safe/big/slatex.rkt")
     (void))))
