#lang typed/racket/base

(provide verifier@)

(require racket/match
         racket/list
         racket/set
         typed/racket/unit
         set-extras
         intern
         bnf
         traces/typed
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


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Visualization
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  #;(: viz : Runnable → Σ)
  #;(define (viz x)
    (define-values (Ξ₀ Σ₀) (inj (comp x #:havoc? #t)))

    (define (Ξ->Ξ* [Ξ : Ξ]) : Ξ*
      ;; depending on mutable state Σ₀
      (match-define (Σ Σᵥ Σₖ Σₐ) Σ₀)
      (Ξ* Ξ Σᵥ (Ver-K-of Σₖ) (hash-ref Σₐ Ξ (λ () ∅))))

    (define Ξ*->Ξ : (Ξ* → Ξ)
      (match-lambda [(Ξ* Ξ _ _ _) Ξ]))
    
    (define ↝₁ : (Ξ* → (℘ Ξ*))
      (λ (Ξ*) (map/set Ξ->Ξ* (↝ (Ξ*->Ξ Ξ*) Σ₀))))

    (define tagger
      (let ([cache:co->sym : (Mutable-HashTable Ξ* Symbol) (make-hash)]
            [cache:blm->sym : (Mutable-HashTable Ξ* Symbol) (make-hash)]
            [cache:sym->Ξ* : (Mutable-HashTable Symbol Ξ*) (make-hasheq)])
        (define (Ξ*->sym [Ξ* : Ξ*])
          (define-values (m prefix)
            (if (Ξ:co? (Ξ*-_0 Ξ*))
                (values cache:co->sym 'c)
                (values cache:blm->sym 'b)))
          (hash-ref! m Ξ* (λ ()
                            (define s (format-symbol "~a~a" prefix (hash-count m)))
                            (hash-set! cache:sym->Ξ* s Ξ*)
                            s)))
        (define (sym->Ξ* [s : Symbol]) (hash-ref cache:sym->Ξ* s))
        (cons Ξ*->sym sym->Ξ*)))
    
    (parameterize ([print-graph #f]
                   [reduction-steps-cutoff 9999])
      (function-traces/tag ↝₁ (Ξ->Ξ* Ξ₀) tagger))
    
    Σ₀)
  )

