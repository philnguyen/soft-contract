#lang typed/racket/base

(provide sat-result@)

(require typed/racket/unit
         racket/set
         racket/match
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt")

(define-unit sat-result@
  (import)
  (export sat-result^) 

  (: ⊔ : ?Dec ?Dec * → ?Dec)
  (define (⊔ r₁ . rs) (foldl ⊔₁ r₁ rs))

  (: ⊔* (∀ (X) (X → ?Dec) (Listof X) → ?Dec))
  (define (⊔* f xs)
    (for/fold ([r : ?Dec (f (car xs))])
              ([x (in-list (cdr xs))] #:break (not r))
      (⊔₁ r (f x))))

  (: ⊔*/set (∀ (X) (X → ?Dec) (Setof X) → ?Dec))
  (define (⊔*/set f xs)
    (if (set-empty? xs)
        #f
        (for/fold ([r : ?Dec (f (set-first xs))])
                  ([x (in-set (set-rest xs))] #:break (not r))
          (⊔₁ r (f x)))))

  (: neg : ?Dec → ?Dec)
  ;; Negate provability result
  (define (neg r)
    (case r
      [(✓) '✗]
      [(✗) '✓]
      [else #f]))

  (: bool->Dec : Boolean → Dec)
  (define (bool->Dec x) (if x '✓ '✗))

  (: ⊔₁ : ?Dec ?Dec → ?Dec)
  (define (⊔₁ r₁ r₂) (and r₁ r₂ (eq? r₁ r₂) r₁))
  )
