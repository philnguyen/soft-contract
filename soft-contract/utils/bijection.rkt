#lang typed/racket/base

(provide (all-defined-out))

(require racket/match)

(struct Bij ([fw : (Immutable-HashTable Integer Integer)] [bw : (Immutable-HashTable Integer Integer)]) #:transparent)

(define Bij-empty (Bij (hasheq) (hasheq)))

(: Bij-ext : Bij Integer Integer → (Option Bij))
(define (Bij-ext m x y)
  (match-define (Bij mxy myx) m)
  (match* ((hash-ref mxy x #f) (hash-ref myx y #f))
    [(#f     #f    ) (Bij (hash-set mxy x y) (hash-set myx y x))]
    [((== y) (== x)) m]
    [(_      _     ) #f]))

(: Bij-ref (∀ (X) ([Bij Integer] [(→ X)] . ->* . (U Integer X))))
(define (Bij-ref bij x [default (λ () (error 'Bij-ref "nothing at ~a" x))])
  (hash-ref (Bij-fw bij) x default))

(: Bij-rev-ref (∀ (X) ([Bij Integer] [(→ X)] . ->* . (U Integer X))))
(define (Bij-rev-ref bij y [default (λ () (error 'Bij-rev-ref "nothing at ~a" y))])
  (hash-ref (Bij-bw bij) y default))

(module+ test
  (require typed/rackunit)
  (define m₁ (Bij-ext Bij-empty 1 2))
  (define m₂ (Bij-ext (assert m₁) 1 3))
  (define m₃ (Bij-ext (assert m₁) 1 2))
  (check-equal? (Bij-ref     (assert m₁) 1) 2)
  (check-equal? (Bij-rev-ref (assert m₁) 2) 1)
  (check-false m₂)
  (check-equal? m₁ m₃))
