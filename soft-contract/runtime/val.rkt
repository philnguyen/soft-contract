#lang typed/racket/base

(provide (all-defined-out))

(require racket/match "../ast/definition.rkt" "definition.rkt")

;; Constants & 'Macros'
(define -Null -null)
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -●/V (-●))
(define -●/Vs : (List -V) (list -●/V))
(define -Void/Vs (list (-b (void))))
(define -Void/W (-W -Void/Vs (-b (void))))
(define -not/W (-W¹ 'not 'not))
(define -integer?/W (-W¹ 'integer? 'integer?))
(define -number?/W (-W¹ 'number? 'number?))
(define -vector?/W (-W¹ 'vector? 'vector?))
(define -procedure?/W (-W¹ 'procedure? 'procedure?))
(define -vector-ref/W (-W¹ 'vector-ref 'vector-ref))
(define -vector-set/W (-W¹ 'vector-set! 'vector-set!))
(define -arity-includes?/W (-W¹ 'arity-includes? 'arity-includes?))
(define -=/W (-W¹ '= '=))
(define -contract-first-order-passes?/W (-W¹ 'contract-first-order-passes? 'contract-first-order-passes?))
(define -vector-length/W (-W¹ 'vector-length 'vector-length))
(define -Vector₀ (-Vector '()))
;(define (-=/C [n : Integer]) (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) 0) ⊥ρ))
;(define (-not/C [v : -v]) (-Clo '(x) (-@ 'not (list (-@ v (list (-x 'x)) 0)) 0) ⊥ρ))

(: C-flat? : -V → Boolean)
;; Check whether contract is flat, assuming it's already a contract
(define (C-flat? V)
  (match V
    [(-And/C flat? _ _) flat?]
    [(-Or/C flat? _ _) flat?]
    [(? -Not/C?) #t]
    [(-St/C flat? _ _) flat?]
    [(or (? -Vectorof?) (? -Vector/C?)) #f]
    [(? -=>_?) #f]
    [(or (? -Clo?) (? -Ar?) (? -prim?)) #t]
    [(? -x/C?) #t]
    [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

(: supply-negative-party : Mon-Party -V → -V)
;; Supply the negative party for blaming
(define (supply-negative-party l V)
  (match V
    [(-Ar C α (Mon-Info l+ 'dummy lo))
     (-Ar C α (Mon-Info l+ l      lo))]
    [(-St* s αs α (Mon-Info l+ 'dummy lo))
     (-St* s αs α (Mon-Info l+ l      lo))]
    [(-Vector/hetero αs (Mon-Info l+ 'dummy lo))
     (-Vector/hetero αs (Mon-Info l+ l      lo))]
    [(-Vector/homo α (Mon-Info l+ 'dummy lo))
     (-Vector/homo α (Mon-Info l+ l      lo))]
    [_ V]))
