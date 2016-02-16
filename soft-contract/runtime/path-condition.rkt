#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/set
 "../utils/main.rkt" "../ast/main.rkt")

;; Symbolic value is either pure, refinable expression, or the conservative unrefinable `#f`
(-s . ::= . -e #f)

;; Path condition is set of (pure) expression known to have evaluated to non-#f
(define-type -Γ (℘ -e))
(define ⊤Γ : -Γ ∅) ; the more it grows, the more precise

;; Strengthen path condition `Γ` with `s`
(define (Γ+ [Γ : -Γ] [s : -s])
  (if s (set-add Γ s) Γ))

;; Mapping remembering the "canonicalization" of a variable in terms of the lexically farthest possible variable(s)
(define-type -𝒳 (HashTable Symbol -e))
(define ⊤𝒳 : -𝒳 (hash)) ; the more it grows, the more precise

;; Return an expression canonicalizing given variable in terms of lexically farthest possible variable(s)
(define (canonicalize [𝒳 : -𝒳] [x : Symbol])
  (hash-ref 𝒳 x (λ () (-x x))))

;; Return an expression canonicalizing given expression in terms of lexically farthest possible variable(s)
(define (canonicalize-e [𝒳 : -𝒳] [e : -e])
  ((e/map (for/hash : (HashTable -e -e) ([(x e-x) 𝒳])
            (values (-x x) e-x)))
   e))


(module+ test
  (require typed/rackunit)

  (check-equal? (Γ+ ⊤Γ #f) ⊤Γ)
  (check-equal? (Γ+ ⊤Γ (-x 'x)) {set (-x 'x)})
  (check-equal? (canonicalize-e {hash 'x (-@ '+ (list (-b 1) (-b 2)) -Λ)}
                                (-@ '+ (list (-x 'x) (-x 'y)) -Λ))
                (-@ '+ (list (-@ '+ (list (-b 1) (-b 2)) -Λ) (-x 'y)) -Λ)))
