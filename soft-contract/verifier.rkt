#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         racket/set
         racket/port
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

(define-unit verifier@
  (import parser^
          meta-functions^ static-info^
          sto^ pretty-print^
          exec^ hv^)
  (export verifier^)

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))

  (: run : Runnable → (Values (℘ Err) $))
  (define (run x)
    (with-initialized-static-info
      (exec (if (list? x) (-prog (parse-files x)) x))))

  (: verify-modules : (Listof Path-String) (Listof Syntax) → (Listof Serialized-Blm))
  (define (verify-modules fns stxs)
    (with-initialized-static-info
      (define ms (parse-stxs fns stxs))
      (define-values (es _) (exec (-prog `(,@ms ,(-module 'havoc (list (gen-havoc-expr ms)))))))
      ;; HACK to use `log-debug` instead of `printf`
      (log-debug (with-output-to-string (λ () (print-blames es))))
      (set-map (set-filter Blm? es) serialize-Blm)))

  (: havoc : (Listof Path-String) → (Values (℘ Err) $))
  (define (havoc ps)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (exec (-prog `(,@ms ,(-module 'havoc (list (gen-havoc-expr ms))))))))

  (: havoc/profile ([(Listof Path-String)]
                    [#:delay Positive-Real]
                    . ->* . (Values (℘ Err) $)))
  (define (havoc/profile ps #:delay [delay 0.00001])
    (profile2 (havoc ps) #:delay delay #:order 'self #:use-errortrace? #t))

  (: havoc-last : (Listof Path-String) → (Values (℘ Err) $))
  (define (havoc-last ps)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (define hv (-module 'havoc (list (gen-havoc-expr (list (last ms))))))
      (exec (-prog `(,@ms ,hv)))))

  (define serialize-Blm : (Blm → Serialized-Blm)
    (let ([serialize-ℓ (λ ([ℓ : ℓ]) (list (ℓ-src ℓ) (ℓ-line ℓ) (ℓ-col ℓ)))])
      (match-lambda
        [(Blm party site origin ctc val)
         (list party (serialize-ℓ site) (serialize-ℓ origin) (show-W ctc) (show-W val))])))
  )

