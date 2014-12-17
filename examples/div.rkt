#lang soft-contract

(module div racket
  (provide/contract
   [f ((integer? integer? . -> . integer?) integer? integer? integer? integer? . -> . real?)])
  (define (f g a b c d)
    (/ 1 (- 10 (* (g a b) (g c d))))))

#;(require 'div)
#;((λ (x) (x (λ (x y) ((λ (x) 1) y)) 0 0 0 0)) f)
