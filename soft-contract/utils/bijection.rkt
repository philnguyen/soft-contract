#lang typed/racket/base

(provide (all-defined-out))

(require racket/match)

(struct (X Y) Bij ([fw : (Immutable-HashTable X Y)] [bw : (Immutable-HashTable Y X)]) #:transparent)

(define Bij-empty ((inst Bij Nothing Nothing) (hash) (hash)))

(: Bij-ext (∀ (X Y) (Bij X Y) X Y → (Option (Bij X Y))))
(define (Bij-ext m x y)
  (match-define (Bij mxy myx) m)
  (match* ((hash-ref mxy x #f) (hash-ref myx y #f))
    [(#f     #f    ) (Bij (hash-set mxy x y) (hash-set myx y x))]
    [((== y) (== x)) m]
    [(_      _     ) #f]))

(: Bij-ref (∀ (X Y Z) ([(Bij X Y) X] [(→ Z)] . ->* . (U Y Z))))
(define (Bij-ref bij x [default (λ () (error 'Bij-ref "nothing at ~a" x))])
  (hash-ref (Bij-fw bij) x default))

(: Bij-rev-ref (∀ (X Y Z) ([(Bij X Y) Y] [(→ Z)] . ->* . (U X Z))))
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
