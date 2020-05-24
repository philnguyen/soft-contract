#lang racket/base

(require soft-contract/fake-contract)

(define (Y f) ((λ (q) (f (λ (s) ((q q) s)))) (λ (q) (f (λ (s) ((q q) s))))))
(define (((h b) f) n) (if (zero? n) (f 1) (f ((b f) (sub1 n)))))
(define ((g a) m) (if (zero? m) add1 ((Y h) (a (sub1 m)))))
(define (ack m n) (((Y g) m) n))

(provide
 (contract-out
  [ack (exact-nonnegative-integer? exact-nonnegative-integer? . -> . exact-nonnegative-integer? #:total? #t)]))
