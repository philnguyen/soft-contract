#lang racket

(define x 20)
(define y 30)
(define z 40)

(provide
 (contract-out [x positive?]
               [y byte?]
               [z fixnum?]))
