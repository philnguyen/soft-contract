#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/function racket/set
 "../utils/def.rkt" "../utils/map.rkt" "../utils/set.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "env.rkt" "path-inv.rkt" "addr.rkt")

;; blessed arrow, struct, and closed lambda, etc.
(define-data -V
  'undefined
  -prim
  (struct -●)
  ;; Structs
  (struct -St [info : -struct-info] [fields : (Listof (U -α.fld -α.var-car -α.var-cdr))])
  (struct -St/checked
    [info : -struct-info] [contracts : (Listof (Option -α))] [mon : Mon-Info]
    [unchecked : -α.st*])
  ;; Vectors
  (struct -Vector [fields : (Listof -α.idx)])
  (struct -Vector/checked [contracts : (Listof -α)] [mon : Mon-Info] [unchecked : -α.vct])
  ;; Functions
  (struct -Clo* [xs : -formals] [e : -e] [ρ : -ρ]) ; unescaped closure
  (struct -Clo [xs : -formals] [e : -e] [ρ : -ρ] [Γ : -Γ])
  (struct -Ar [#|ok, no recursion|# guard : -=>i] [v : (Pairof -α -?e)] [l³ : Mon-Info])
  ;; Contracts
  ; Treat `and/c`, `or/c` specially to deal with `chaperone?`
  ; But these give rise to more special cases of stack frames
  (struct -And/C [flat? : Boolean] [l : -α.and/c-l] [r : -α.and/c-r])
  (struct -Or/C [flat? : Boolean] [l : -α.or/c-l] [r : -α.or/c-r])
  (struct -Not/C [γ : -α.not/c])
  (struct -Vectorof [γ : -α.vectorof])
  (struct -Vector/C [γs : (Listof -α.vector/c)])
  (struct -St/C [flat? : Boolean] [info : -struct-info] [fields : (Listof -α.struct/c)])
  (struct -=>i
    [doms : (Listof (List Symbol -?e -α))]
    [rst : (Option (List Symbol -?e -α))]
    [rng : -e] [env : -ρ] [Γ : -Γ])
  (struct -x/C [c : -α.x/c])
  )
(define-type -Vs (Listof -V))

(define-data -A
  -Vs
  (struct -blm [violator : Mon-Party] [origin : Mon-Party] [v : -V] [c : -Vs]))

;; Use this adhoc type instead of `cons` to avoid using `inst`
(struct -AΓ ([A : -A] [Γ : -Γ]) #:transparent)
(define-type -AΓs (U -AΓ (Setof -AΓ)))

;; `X` paired with expression
(struct (X) -W ([x : X] [e : -?e]) #:transparent)

(define-type/pred -WV (-W -V))
(define-type -WVs (-W (Listof -V)))

(define (WVs->Vs [WVs : (Listof -WV)]) : -Vs
  ((inst map -V -WV) -W-x WVs))

(: close : -v -ρ → -V)
;; Create closure from value syntax and environment
(define (close v ρ)
  (match v
    [(-λ xs e) (-Clo* xs e (ρ↓ ρ (FV v)))]
    [(? -prim? v) v]
    [(? -•?) -●/V]
    [_ (error 'close "Not yet supported: ~a" v)]))

(: close-Γ (case-> [-Γ -V → -V]
                   [-Γ (Listof -V) → (Listof -V)]))
(define (close-Γ Γ V)
  (match V
    [(-Clo* xs e ρ)
     (-Clo xs e ρ (Γ↓ Γ (dom ρ)))]
    [(list Vs ...) (map (curry close-Γ Γ) Vs)]
    [(? -V?) V]))

(: C-flat? : -V → Boolean)
;; Check whether contract is flat, assuming it's already a contract
(define (C-flat? V)
  (match V
    [(-And/C flat? _ _) flat?]
    [(-Or/C flat? _ _) flat?]
    [(? -Not/C?) #t]
    [(-St/C flat? _ _) flat?]
    [(or (? -Vectorof?) (? -Vector/C?)) #f]
    [(? -=>i?) #f]
    [(or (? -Clo*?) (? -Clo?) (? -Ar?) (? -prim?)) #t]
    [(? -x/C?) #t]
    [V (error 'C-flat? "Unepxected: ~a" (show-V V))]))

;; Pretty-print evaluated value
(define (show-V [V : -V]) : Sexp
  (match V
    ['undefined 'undefined]
    [(-b b) (show-b b)]
    [(-●) '●]
    [(? -o? o) (show-o o)]
    [(-Clo* xs e _) (show-e (-λ xs e))]
    [(-Clo xs e _ _) (show-e (-λ xs e))]
    [(-Ar guard (cons α ?e) l³) `(,(show-V guard) ◃ (,(show-α α) @ ,(show-?e ?e)))]
    [(-St s αs) `(,(show-struct-info s) ,@(map show-α αs))]
    [(-St/checked s γs _ α)
     `(,(string->symbol (format "~a/wrapped" (show-struct-info s)))
       ,@(for/list : (Listof Symbol) ([γ γs]) (if γ (show-α γ) '✓))
       ▹ ,(show-α α))]
    [(-Vector αs) `(vector ,@(map show-α αs))]
    [(-Vector/checked γs _ α) `(vector/wrapped ,@(map show-α γs) ▹ ,(show-α α))]
    [(-And/C _ l r) `(and/c ,(show-α l) ,(show-α r))]
    [(-Or/C _ l r) `(or/c ,(show-α l) ,(show-α r))]
    [(-Not/C γ) `(not/c ,(show-α γ))]
    [(-Vectorof γ) `(vectorof ,(show-α γ))]
    [(-Vector/C γs) `(vector/c ,@(map show-α γs))]
    [(-=>i doms rst d ρ Γ)
     (define-values (xs cs)
       (for/lists ([xs : (Listof Symbol)] [cs : (Listof -?e)])
                  ([dom : (List Symbol -?e -α) doms])
         (match-define (list x c _) dom)
         (values x c)))
     (define dep? (not (set-empty? (∩ (FV d) (list->set xs)))))
     (match* (dep? rst)
       [(#f #f)
        `(,@(map show-?e cs) . -> . ,(show-e d))]
       [(#f (list x* c* γ*))
        `(,(map show-?e cs) #:rest ,(show-?e c*) . ->* . ,(show-e d))]
       [(#t #f)
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-?e c)))
              (res ,xs ,(show-e d)))]
       [(#t (list x* c* γ*))
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-?e c)))
              #:rest (,x* ,(show-?e c*))
              (res ,xs ,(show-e d)))])]
    [(-St/C _ s αs)
     `(,(string->symbol (format "~a/c" (show-struct-info s))) ,@(map show-α αs))]
    [(-x/C (-α.x/c x)) `(recursive-contract ,(show-x/c x))]))

(define (show-A [A : -A]) : Sexp
  (match A
    [(-blm l+ lo V C) `(blame ,l+ ,lo ,(show-V V) ,(map show-V C))]
    [(? list? Vs) (map show-V Vs)]))

(define (show-WV [WV : -WV]) : (Listof Sexp)
  (match-define (-W V e) WV)
  `(,(show-V V) @ ,(show-?e e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants & 'Macros'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -Null -null)
(define -Any/C (-Clo '(x) -tt -ρ⊥ -Γ⊤))
(define -True/Vs  (list -tt))
(define -False/Vs (list -ff))
(define -●/V (-●))
(define -Void/Vs (list (-b (void))))
(define -Void/W (-W -Void/Vs (-b (void))))
(define -integer?/W (-W 'integer? 'integer?))
(define -number?/W (-W 'number? 'number?))
(define -vector?/W (-W 'vector? 'vector?))
(define -procedure?/W (-W 'procedure? 'procedure?))
(define -vector-ref/W (-W 'vector-ref 'vector-ref))
(define -vector-set/W (-W 'vector-set! 'vector-set!))
(define -arity-includes?/W (-W 'arity-includes? 'arity-includes?))
(define -=/W (-W '= '=))
(define -contract-first-order-passes?/W
  (-W 'contract-first-order-passes? 'contract-first-order-passes?))
(define -Vector₀ (-Vector '()))

(define (-=/C [n : Integer])
  (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤))

(define (-not/C [v : -v])
  (-Clo '(x) (-@ 'not (list (-@ v (list (-x 'x)) -Λ)) -Λ) -ρ⊥ -Γ⊤))