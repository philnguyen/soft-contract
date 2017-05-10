#lang racket/base

(require
  "structs.rkt"
  "benv.rkt"
)

;; ---

(provide
  time-zero
  k
  tick
  alloc
)

;; =============================================================================

;; ---
;(define-type Value Closure)

;(: take* (All (A) (-> (Listof A) Natural (Listof A))))
(define (take* l n)
  (for/list ([e (in-list l)]
             [i (in-range n)])
    e))

;; ---

;(: time-zero Time)
(define time-zero '())

;(: k (Parameterof Natural))
(define k (make-parameter 1))

;(: tick (-> Stx Time Time))
(define (tick call time)
  (define label (Stx-label call))
  (take* (cons label time) (k)))

;(: alloc (-> Time (-> Var Addr)))
(define ((alloc time) var)
  (Binding var time))

