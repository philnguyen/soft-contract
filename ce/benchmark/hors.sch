(module c racket (provide/contract [c (integer? . -> . any/c)])
  (define (c _) 'unit))

(module b racket (provide/contract [b ((integer? . -> . any/c) integer? . -> . any/c)])
  (define (b x _) (x 1)))

(module a racket (provide/contract [a ((integer? . -> . any/c) (integer? . -> . any/c) zero? . -> . any/c)])
  (define (a x y q) (begin (x 0) (y 0))))

(module f racket (provide/contract [f (integer? (integer? . -> . any/c) integer? . -> . any/c)])
  (require (submod ".." a) (submod ".." b))
  (define (f n x q)
    (if (<= n 0) (x q)
        (a x (λ (p) (f (- n 1) (λ (_) (b x _)) p)) q))))

(module s racket (provide/contract [s (integer? integer? . -> . any/c)])
  (require (submod ".." c) (submod ".." f))
  (define (s n q) (f n c q)))

(module main racket (provide/contract [main (integer? . -> . any/c)])
  (require (submod ".." s))
  (define (main n) (s n 0)))

(require 'main)
(main •)
