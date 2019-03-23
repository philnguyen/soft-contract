#lang racket

(define x 20)
(define y 30)
(define z 40)
(define v (void))

(provide
 (contract-out [x positive?]
               [y byte?]
               [z fixnum?]
               [v (λ (x) (equal? x (void)))]))
