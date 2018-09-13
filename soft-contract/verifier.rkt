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
         "reduction/signatures.rkt"
         )

(require (only-in typed/racket/unsafe unsafe-require/typed))
(unsafe-require/typed redex/gui
  [reduction-steps-cutoff (Parameterof Natural)])

(define-interner Ver-V Σᵥ)
(define-interner Ver-K Σₖ)
(define-interner Ver-A Σₐ)
(Ξ* . ::= . (Ξ* Ξ Σᵥ Ver-K R^))

(define-unit verifier@
  (import parser^
          static-info^
          sto^
          step^ compile^ (prefix hv: havoc^))
  (export verifier^)

  (define-syntax-rule (with-initialized-static-info e ...)
    (parameterize ([current-static-info (new-static-info)])
      e ...))

  (: run : Runnable → (Values (℘ Blm) Σ))
  (define (run x)
    (with-initialized-static-info
      (↝* (comp x))))

  (: havoc : (Listof Path-String) → (Values (℘ Blm) Σ))
  (define (havoc ps)
    (with-initialized-static-info
      (↝* (comp ps #:havoc? #t))))

  (: havoc/profile ([(Listof Path-String)]
                    [#:delay Positive-Real]
                    . ->* . (Values (℘ Blm) Σ)))
  (define (havoc/profile ps #:delay [delay 0.05])
    (let ([ans : (℘ Blm) ∅]
          [Σ : (Option Σ) #f])
      ((inst profile-thunk Void)
       (λ () (set!-values (ans Σ) (havoc ps))) #:delay delay)
      (values ans (assert Σ))))

  (: havoc-last : (Listof Path-String) → (Values (℘ Blm) Σ))
  (define (havoc-last ps)
    (with-initialized-static-info
      (define ms (parse-files ps))
      (define hv (-module 'havoc (list (hv:gen-havoc-expr (list (last ms))))))
      (↝* (↓ₚ (-prog `(,@ms ,hv))))))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Visualization
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: viz : Runnable → Σ)
  (define (viz x)
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

  (: comp ([Runnable] [#:havoc? Boolean] . ->* . ⟦E⟧))
  (define (comp x #:havoc? [havoc? #f])
    (define (maybe-with-hv [ms : (Listof -module)])
      (if havoc?
          `(,@ms ,(-module 'havoc (list (hv:gen-havoc-expr ms))))
          ms))
    (cond [(-prog? x) (↓ₚ (-prog (maybe-with-hv (-prog-_0 x))))]
          [(list? x) (↓ₚ (-prog (maybe-with-hv (parse-files x))))]
          [else (↓ₑ 'top-level x)]))
  )

