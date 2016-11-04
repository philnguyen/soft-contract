#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "definition.rkt"
         "sto.rkt")

;; Constants & 'Macros'
(define -Null -null)
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -True/W  (-W -True/Vs  -tt))
(define -False/W (-W -False/Vs -ff))
(define -●/V (-● ∅))
(define -●/Vs (list -●/V))
(define -Bool/Vs (list (-● {set 'boolean?})))
(define -Nat/Vs (list (-● {set 'exact-nonnegative-integer?})))
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
(define -Zero/W (-W¹ -zero -zero))
(define -unsafe-struct-ref/W (-W¹ 'unsafe-struct-ref 'unsafe-struct-ref))
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

(: supply-negative-party : -l -V → -V)
;; Supply the negative party for blaming
(define (supply-negative-party l V)
  (match V
    [(-Ar C α (-l³ l+ 'dummy lo))
     (-Ar C α (-l³ l+ l      lo))]
    [(-St* s αs α (-l³ l+ 'dummy lo))
     (-St* s αs α (-l³ l+ l      lo))]
    [(-Vector/hetero αs (-l³ l+ 'dummy lo))
     (-Vector/hetero αs (-l³ l+ l      lo))]
    [(-Vector/homo α (-l³ l+ 'dummy lo))
     (-Vector/homo α (-l³ l+ l      lo))]
    [_ V]))

(define printing : (HashTable (List -V (U -e -V)) Void) (make-hash))

(: behavioral? : -σ -V → Boolean)
;; Check if value maybe behavioral.
;; `#t` is a conservative answer "maybe yes"
;; `#f` is a strong answer "definitely no"
(define (behavioral? σ V)
  (define-set seen : -V #:eq? #t)

  (: check-α! : -α → Boolean)
  (define (check-α! α)
    (for/or ([V (σ@ᵥ σ α)])
      (check! V)))

  (: check! : -V → Boolean)
  (define (check! V)
    (cond
      [(seen-has? V) #f]
      [else
       (seen-add! V)
       (match V
         [(-St _ αs) (ormap check-α! αs)]
         [(-St* _ _ α _) (check-α! α)]
         [(-Vector αs) (ormap check-α! αs)]
         [(-Ar grd α _) (or (check-α! α) (check! grd))]
         [(-=> doms rng _)
          (or (check-α! (car rng))
              (for/or : Boolean ([dom doms])
                (check-α! (car dom))))]
         [(? -=>i?) #t]
         [(-Case-> cases _)
          (for*/or : Boolean ([kase : (Pairof (Listof -α) -α) cases])
            (match-define (cons doms rng) kase)
            (or (check-α! rng)
                (ormap check-α! doms)))]
         [(or (? -Clo?) (? -Case-Clo?)) #t]
         [_ #f])]))

  (check! V))
