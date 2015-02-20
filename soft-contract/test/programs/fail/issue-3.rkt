#lang racket
(require soft-contract/fake-contract)

(define x "hi")

(provide
 (contract-out [x integer?]))
