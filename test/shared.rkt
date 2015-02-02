#lang racket/base
(provide (all-defined-out))
(require racket/contract
         racket/set
         racket/match
         "../lang.rkt"
         "../runtime.rkt"
         (only-in "../delta.rkt" δ refine))

(define/contract (● . Cs)
  ([] [] #:rest (listof .V?) . ->* . .//?)
  (.// '• (list->set Cs)))
