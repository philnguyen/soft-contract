#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         typed/racket/unit
         set-extras
         "utils/main.rkt"
         "ast/main.rkt"
         "runtime/signatures.rkt"
         "signatures.rkt"
         "reduction/signatures.rkt"
         )

(define-unit verifier@
  (import reduction^ compile^ parser^ havoc^)
  (export verifier^)
  
  (define (run-files [ps : (Listof Path-String)]) : (Values (℘ -ΓA) -Σ)
    (with-initialized-static-info
      (run (↓ₚ (parse-files ps) -void))))

  (define (havoc-files [ps : (Listof Path-String)]) : (Values (℘ -ΓA) -Σ)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (run (↓ₚ ms (gen-havoc-expr ms)))))

  (define (havoc-last-file [ps : (Listof Path-String)]) : (Values (℘ -ΓA) -Σ)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (run (↓ₚ ms (gen-havoc-expr (list (last ms)))))))

  (define (run-e [e : -e]) : (Values (℘ -ΓA) -Σ)
    (with-initialized-static-info
      (run (↓ₑ 'top e))))

  (define-parameter debug-iter? : Boolean #f)
  (define-parameter debug-trace? : Boolean #f)
  (define-parameter max-steps : Natural (expt 2 31)))

