#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/set
 "../utils/set.rkt" "../utils/map.rkt"
 "../ast/definition.rkt"
 "path-inv.rkt" "val.rkt")

(struct -Res ([e : -?e] [facts : -es]) #:transparent)
(define -Res⊤ (-Res #f ∅))
(define-type -M (MMap -e -Res))
(define-type -ΔM (ΔMap -e -Res))
(define -M⊥ : -M (hash))

(: M⊔ : -M -e -WVs -es → -M)
;; Update summarization table
(define (M⊔ M e W es)
  (match-define (-W _ ?e) W)
  (⊔ M e (-Res ?e es)))

(define (show-Res [r : -Res]) : (Listof Sexp)
  (match-define (-Res e es) r)
  `(,(show-?e e) : ,@(show-es es)))

(define (show-M [M : -M]) : (Listof Sexp)
  (for/list : (Listof Sexp) ([(e Reses) M])
    `(,(show-e e) ↝⋆ ,@(set-map Reses show-Res))))
