#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base racket/syntax syntax/parse)
         racket/match
         racket/set
         racket/splicing
         syntax/parse/define
         set-extras
         "../utils/main.rkt"
         "../ast/definition.rkt"
         "../ast/shorthands.rkt"
         "definition.rkt"
         "sto.rkt")

;; Constants & 'Macros'
(define-syntax-parser def-val
  [(_ id:id V:expr v:expr)
   (define/with-syntax id.V  (format-id #'id "~a.V"  (syntax-e #'id)))
   (define/with-syntax id.W¹ (format-id #'id "~a.W¹" (syntax-e #'id)))
   (define/with-syntax id.Vs (format-id #'id "~a.Vs" (syntax-e #'id)))
   (define/with-syntax id.W  (format-id #'id "~a.W"  (syntax-e #'id)))
   #'(splicing-let ([sᵥ v])
       (define id.V V)
       (define id.W¹ (-W¹ id.V sᵥ))
       (define id.Vs (list id.V))
       (define id.W (-W id.Vs sᵥ)))]
  [(_ id:id v)
   #'(def-val id v v)]
  [(_ id:id)
   #'(def-val id id id)])

(def-val -null)
(def-val -null-char)
(def-val -tt)
(def-val -ff)
(def-val -● (-● ∅) #f)
(define -Bool.Vs (list (-● {set 'boolean?})))
(define -Nat.V (-● {set 'exact-nonnegative-integer?}))
(define -Nat.Vs (list -Nat.V))
(define -PosNat.V (-● {set 'exact-positive-integer?}))
(define -PosNat.Vs (list -PosNat.V))
(def-val -void)
(def-val -apply 'apply)
(def-val -any/c 'any/c)
(def-val -none/c 'none/c)
(def-val -not 'not)
(def-val -integer? 'integer?)
(def-val -number? 'number?)
(def-val -vector 'vector)
(def-val -make-vector 'make-vector)
(def-val -vector? 'vector?)
(def-val -procedure? 'procedure?)
(def-val -vector-ref 'vector-ref)
(def-val -vector-set! 'vector-set!)
(def-val -arity-includes? 'arity-includes?)
(def-val -= '=)
(def-val -contract-first-order-passes? 'contract-first-order-passes?)
(def-val -vector-length 'vector-length)
(define -Vector₀ (-Vector '()))
(def-val -zero)
(def-val -unsafe-struct-ref 'unsafe-struct-ref)
(define -Empty-Values.W (-W '() (-t.@ 'values '())))
;(define (-=/C [n : Integer]) (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) 0) ⊥ρ))
;(define (-not/C [v : -v]) (-Clo '(x) (-@ 'not (list (-@ v (list (-x 'x)) 0)) 0) ⊥ρ))

(: C-flat? : -V → Boolean)
;; Check whether contract is flat, assuming it's already a contract
(define (C-flat? V)
  (match V
    [(-And/C flat? _ _) flat?]
    [(-Or/C flat? _ _) flat?]
    [(? -Not/C?) #t]
    [(? -One-Of/C?) #t]
    [(-St/C flat? _ _) flat?]
    [(or (? -Vectorof?) (? -Vector/C?)) #f]
    [(? -=>_?) #f]
    [(or (? -Clo?) (? -Ar?) (? -prim?)) #t]
    [(? -x/C?) #t]
    [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

(: with-negative-party : -l -V → -V)
;; Supply the negative party for blaming
(define (with-negative-party l V)
  (match V
    [(-Ar C α (-l³ l+ _ lo))
     (-Ar C α (-l³ l+ l lo))]
    [(-St* grd α (-l³ l+ _ lo))
     (-St* grd α (-l³ l+ l lo))]
    [(-Vector/guard grd ⟪α⟫ (-l³ l+ _ lo))
     (-Vector/guard grd ⟪α⟫ (-l³ l+ l lo))]
    [_ V]))

(: with-positive-party : -l -V → -V)
(define (with-positive-party l V)
  (match V
    [(-Ar C α (-l³ _ l- lo))
     (-Ar C α (-l³ l l- lo))]
    [(-St* grd α (-l³ _ l- lo))
     (-St* grd α (-l³ l l- lo))]
    [(-Vector/guard grd ⟪α⟫ (-l³ _ l- lo))
     (-Vector/guard grd ⟪α⟫ (-l³ l l- lo))]
    [_ V]))

(: approximate-under-contract : -V → -V)
(define (approximate-under-contract V)
  (match V
    [(-Ar C _ l³)
     (-Ar C ⟪α⟫ₒₚ l³)]
    [(-St* C _ l³)
     (-St* C ⟪α⟫ₒₚ l³)]
    [(-Vector/guard C _ l³)
     (-Vector/guard C ⟪α⟫ₒₚ l³)]
    [_ V]))

(: behavioral? : -σ -V → Boolean)
;; Check if value maybe behavioral.
;; `#t` is a conservative answer "maybe yes"
;; `#f` is a strong answer "definitely no"
(define (behavioral? σ V)
  (define-set seen : ⟪α⟫ #:eq? #t #:as-mutable-hash? #t)

  (: check-⟪α⟫! : ⟪α⟫ → Boolean)
  (define (check-⟪α⟫! ⟪α⟫)
    (cond [(seen-has? ⟪α⟫) #f]
          [else
           (seen-add! ⟪α⟫)
           (for/or ([V (σ@ σ ⟪α⟫)])
             (check! V))]))

  (: check! : -V → Boolean)
  (define (check! V)
    (match V
      [(-St _ αs) (ormap check-⟪α⟫! αs)]
      [(-St* _ α _) (check-⟪α⟫! α)]
      [(-Vector αs) (ormap check-⟪α⟫! αs)]
      [(-Vector^ α _) (check-⟪α⟫! α)]
      [(-Ar grd α _) #t]
      [(-=> doms rngs _)
       (match doms
         [(? list? doms)
          (or (for/or : Boolean ([dom (in-list doms)])
                (check-⟪α⟫! (-⟪α⟫ℓ-addr dom)))
              (and (pair? rngs)
                   (for/or : Boolean ([rng (in-list rngs)])
                     (check-⟪α⟫! (-⟪α⟫ℓ-addr rng)))))]
         [(-var doms dom)
          (or (check-⟪α⟫! (-⟪α⟫ℓ-addr dom))
              (for/or : Boolean ([dom (in-list doms)])
                (check-⟪α⟫! (-⟪α⟫ℓ-addr dom)))
              (and (pair? rngs)
                   (for/or : Boolean ([rng (in-list rngs)])
                     (check-⟪α⟫! (-⟪α⟫ℓ-addr rng)))))])]
      [(? -=>i?) #t]
      [(-Case-> cases _)
       (for*/or : Boolean ([kase : (Pairof (Listof ⟪α⟫) ⟪α⟫) cases])
         (match-define (cons doms rng) kase)
         (or (check-⟪α⟫! rng)
             (ormap check-⟪α⟫! doms)))]
      [(or (? -Clo?) (? -Case-Clo?)) #t]
      [_ #f]))

  (check! V))

(define guard-arity : (-=>_ → Arity)
  (match-lambda
    [(-=> αs _ _) (shape αs)]
    [(and grd (-=>i αs (list mk-D mk-d _) _))
     (match mk-D
       [(-Clo xs _ _ _) (shape xs)]
       [_
        ;; FIXME: may be wrong for var-args. Need to have saved more
        (length αs)])]))  
