#lang typed/racket/base

(provide sat-result@)

(require typed/racket/unit
         racket/match
         racket/set
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt")

(define-unit sat-result@
  (import)
  (export sat-result^) 

  (: ⊔ : Valid Valid * → Valid)
  (define (⊔ r₁ . rs) (foldl ⊔₁ r₁ rs))

  (: ⊔* (∀ (X) (X → Valid) (Setof X) → Valid))
  (define (⊔* f xs)
    (for/fold ([r : Valid (f (set-first xs))])
              ([x (in-set (set-rest xs))] #:break (eq? r '?))
      (⊔₁ r (f x))))

  (: neg : Valid → Valid)
  ;; Negate provability result
  (define (neg r)
    (case r
      [(✓) '✗]
      [(✗) '✓]
      [else '?]))

  (: bool->sat : Boolean → (U '✓ '✗))
  (define (bool->sat x) (if x '✓ '✗))

  (define ⊔₁ : (Valid Valid → Valid)
    (match-lambda**
     [('? _) '?]
     [(_ '?) '?]
     [(r₁ r₂) (if (eq? r₁ r₂) r₁ '?)]))
  )
