#lang typed/racket/base

(provide (all-defined-out))
(require typed/rackunit)

(define-syntax-rule (check-✓ e) (check-equal? e '✓))
(define-syntax-rule (check-✗ e) (check-equal? e '✗))
(define-syntax-rule (check-? e) (check-equal? e '?))
