#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         racket/set
         typed/racket/unit
         set-extras
         intern
         bnf
         unreachable
         "utils/main.rkt"
         "ast/signatures.rkt"
         "runtime/signatures.rkt"
         "signatures.rkt"
         "execution/signatures.rkt"
         )

(require (only-in typed/racket/unsafe unsafe-require/typed))
(unsafe-require/typed redex/gui
  [reduction-steps-cutoff (Parameterof Natural)])

(define-unit verifier@
  (import parser^
          meta-functions^ static-info^
          sto^
          exec^ hv^)
  (export verifier^)

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))

  (: run : Runnable → (Values (℘ Err) $))
  (define (run x)
    (with-initialized-static-info
      (exec (if (list? x) (-prog (parse-files x)) x))))

  (: havoc : (Listof Path-String) → (Values (℘ Err) $))
  (define (havoc ps)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (exec (-prog `(,@ms ,(-module 'havoc (list (gen-havoc-expr ms))))))))

  (: optimize : -module (℘ Err) → -module)
  (define (optimize m errs)
    ;; Collect potential sites and contract sources of violation
    (define-values (origins sites)
      (for/fold ([origins : (℘ ℓ) ∅eq] [sites : (℘ ℓ) ∅eq])
                ([err (in-set errs)] #:when (Blm? err))
        (values (set-add origins (Blm-origin err))
                (set-add sites   (Blm-site err)))))
    ;; Split out optimized module
    (optimize-uses sites (optimize-contracts origins m)))

  (: havoc/profile ([(Listof Path-String)]
                    [#:delay Positive-Real]
                    . ->* . (Values (℘ Err) $)))
  (define (havoc/profile ps #:delay [delay 0.001])
    (profile2 (havoc ps) #:delay delay))

  (: havoc-last : (Listof Path-String) → (Values (℘ Err) $))
  (define (havoc-last ps)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (define hv (-module 'havoc (list (gen-havoc-expr (list (last ms))))))
      (exec (-prog `(,@ms ,hv)))))
  )

