#lang typed/racket/base

(provide sat-result@)

(require typed/racket/unit
         racket/sequence
         racket/match
         racket/bool
         racket/set
         racket/splicing
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../proof-relation/signatures.rkt"
         "../primitives/signatures.rkt"
         "signatures.rkt")

(define-unit sat-result@
  (import)
  (export sat-result^) 

  (: R⊔ : -R -R * → -R)
  (define (R⊔ R₁ . Rs)
    (for/fold ([R : -R R₁]) ([Rᵢ (in-list Rs)])
      (⊔ R Rᵢ)))

  (: R⊔* (∀ (X) (X → -R) (Sequenceof X) → -R))
  (define (R⊔* f xs)
    (for/fold ([R : -R (f (sequence-ref xs 0))])
              ([x (sequence-tail xs 0)] #:break (eq? R '?))
      (⊔ R (f x))))

  (: not-R : -R → -R)
  ;; Negate provability result
  (define (not-R R)
    (case R [(✓) '✗] [(✗) '✓] [else '?]))

  (: boolean->R : Boolean → (U '✓ '✗))
  (define (boolean->R x) (if x '✓ '✗))

  (define ⊔ : (-R -R → -R)
    (match-lambda**
     [('? _) '?]
     [(_ '?) '?]
     [(R₁ R₂) (if (eq? R₁ R₂) R₁ '?)]))
  )
