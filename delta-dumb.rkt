#lang racket
(require (only-in "delta.rkt" [Δ Δ1] refine)
         "syntax.rkt"
         "lang.rkt")
(provide Δ refine)

(define (Δ l σ o Vs)
  (match/nd (Δ1 l σ o Vs)
    [(cons σ1 A1) (cons σ (delabel A1 σ1))]))

(define (delabel A σ)
  (match A
    [(? L? l) (delabel (σ@ σ l) σ)]
    [(val U Cs) (match U
                  [(Struct t Vs) (val (Struct t (for/list ([V Vs]) (delabel V σ))) Cs)]
                  [_ A])]
    [_ A]))