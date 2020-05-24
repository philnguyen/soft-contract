#lang racket

(define x 20)
(define y 30)
(define z 40)
(define v (void))

(define (f n) (sub1 n))

(define (g n) (sub1 n))

(provide
 (contract-out [x positive?]
               [y byte?]
               [z fixnum?]
               [v (λ (x) (equal? x (void)))]
               [f ((and/c byte? positive?) . -> . exact-nonnegative-integer?)]
               [g ((and/c fixnum? positive?) . -> . exact-nonnegative-integer?)]))
