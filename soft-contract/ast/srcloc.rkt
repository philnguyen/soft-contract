#lang typed/racket/base
(provide (all-defined-out))

(require racket/match
         "../utils/pretty.rkt"
         "../utils/intern.rkt")

;; Temporary definition of module path
(define-type -l (U Symbol String))
(define-predicate l? -l)

(struct loc ([src : -l]
             [line : Natural]
             [col : Natural]
             [id : (Listof (U Symbol Natural))])
  #:transparent)

(define-interner loc #:interned-type-name ℓ)

;; Dummy
(define +ℓ₀ (loc->ℓ (loc 'dummy 0 0 '())))

(: syntax-ℓ : Any → ℓ) ; domain `Any` to get around contract generation complaint
(define (syntax-ℓ stx)
  (cond [(syntax? stx)
         (define src
           (match (syntax-source stx)
             [(? path? p) (path->string p)]
             [(? l? l) l]
             [src (error 'syntax-ℓ "not valid path: ~a" src)]))
         (define line (assert (syntax-line stx)))
         (define col  (assert (syntax-column stx)))
         (loc->ℓ (loc src line col '()))]
        [else (error 'syntax-ℓ "expect syntax, given ~a" stx)]))

(: ℓ-with-id : ℓ (U Symbol Natural) → ℓ)
(define (ℓ-with-id ℓ id)
  (match-define (loc src line col ids) (ℓ->loc ℓ))
  (loc->ℓ (loc src line col (cons id ids))))

(: ℓ-with-ids : ℓ Natural → (Listof ℓ))
(define (ℓ-with-ids ℓ n)
  (for/list ([i n]) (ℓ-with-id ℓ i)))

(: on-ℓ (∀ (X) (loc → X) → ℓ → X))
(define ((on-ℓ f) ℓ) (f (ℓ->loc ℓ)))

(define ℓ-src (on-ℓ loc-src))
(define ℓ-line (on-ℓ loc-line))
(define ℓ-col  (on-ℓ loc-col))
(define ℓ-id (on-ℓ loc-id))

(define (show-ℓ [ℓ : ℓ])
  (match-define (loc src line col id) (ℓ->loc ℓ))
  (case loc
    [(dummy) '□]
    [else (format-symbol "ℓ~a~a" (n-sub line) (n-sup col))]))
