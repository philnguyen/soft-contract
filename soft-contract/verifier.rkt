#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         typed/racket/unit
         set-extras
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "signatures.rkt"
         "reduction/signatures.rkt"
         )

(define-unit verifier@
  (import static-info^ run^ compile^ parser^)
  (export verifier^)

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))
  
  (define (run-files [ps : (Listof Path-String)]) : (Values (℘ Blm) Σ)
    (with-initialized-static-info
      (run (↓ₚ (-prog (parse-files ps) -void)))))

  #;(define (havoc-files [ps : (Listof Path-String)]) : (Values (℘ Blm) -Σ)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (run (↓ₚ (-prog ms (gen-havoc-expr ms))))))

  #;(: havoc-files/profile
     ([(Listof Path-String)] [#:delay Positive-Real] . ->* . (Values (℘ -A) -Σ)))
  #;(define (havoc-files/profile ps #:delay [delay 0.05])
    (define ans : (℘ -A) ∅)
    (define Σ : (Option -Σ) #f)
    ((inst profile-thunk Void)
     (λ ()
       (set!-values (ans Σ) (havoc-files ps)))
     #:delay delay)
    (values ans (assert Σ)))

  #;(define (havoc-last-file [ps : (Listof Path-String)]) : (Values (℘ -A) -Σ)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (run (↓ₚ ms (gen-havoc-expr (list (last ms)))))))

  (define (run-e [e : -e]) : (Values (℘ Blm) -Σ)
    (with-initialized-static-info
      (run (↓ₑ 'top e))))
  )

