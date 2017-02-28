#lang typed/racket/base

(provide run-file run-files havoc-file havoc-files run-e)

(require racket/match
         "utils/main.rkt"
         "ast/main.rkt"
         "runtime/definition.rkt"
         "parse/main.rkt"
         "reduction/compile/main.rkt"
         "reduction/quick-step.rkt"
         "reduction/havoc.rkt")

(: run-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (run-file p) (run-files (list p)))

(: run-files : (Listof Path-String) → (Values (℘ -ΓA) -Σ))
(define (run-files ps)
  (with-initialized-static-info
    (run (↓ₚ (map file->module ps) -void))))

(: havoc-file : Path-String → (Values (℘ -ΓA) -Σ))
(define (havoc-file p) (havoc-files (list p)))

(: havoc-files : (Listof Path-String) → (Values (℘ -ΓA) -Σ))
(define (havoc-files ps)
  (with-initialized-static-info
    (define ms (map file->module ps))
    (define e (gen-havoc-expr ms))
    (run (↓ₚ ms e))))

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
