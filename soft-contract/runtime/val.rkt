#lang typed/racket/base

(provide (all-defined-out))

(require
 racket/match racket/function racket/set
 "../utils/def.rkt" "../utils/map.rkt" "../utils/set.rkt"
 "../ast/definition.rkt" "../ast/meta-functions.rkt"
 "env.rkt" "path-inv.rkt" "addr.rkt")

;; blessed arrow, struct, and closed lambda, etc.
(-V . ::= . 'undefined
            -prim
            (-●)
            ;; Structs
            (-St -struct-info (Listof (U -α.fld -α.var-car -α.var-cdr)))
            (-St/checked
              [info : -struct-info] [contracts : (Listof (Option -α.struct/c))] [mon : Mon-Info]
              [unchecked : -α.st*])
            ;; Vectors
            (-Vector (Listof -α.idx))
            (-Vector/checked [contracts : (Listof -α.vector/c)] [mon : Mon-Info] [unchecked : -α.vct])
            (-Vector/same [contract : -α.vectorof] [mon : Mon-Info] [unchecked : -α.vct])
            ;; Functions
            (-Clo* -formals -e -ρ) ; unescaped closure
            (-Clo -formals -e -ρ -Γ)
            (-Ar [#|ok, no recursion|# guard : -=>i] [v : (Pairof -α -?e)] [l³ : Mon-Info])
            ;; Contracts
            ; Treat `and/c`, `or/c` specially to deal with `chaperone?`
            ; But these give rise to more special cases of stack frames
            (-And/C [flat? : Boolean] [l : -α.and/c-l] [r : -α.and/c-r])
            (-Or/C [flat? : Boolean] [l : -α.or/c-l] [r : -α.or/c-r])
            (-Not/C [γ : -α.not/c])
            (-Vectorof [γ : -α.vectorof])
            (-Vector/C [γs : (Listof -α.vector/c)])
            (-St/C [flat? : Boolean] [info : -struct-info] [fields : (Listof -α.struct/c)])
            (-=>i
              [doms : (Listof (Pairof Symbol -α.dom))]
              [rst : (Option (Pairof Symbol -α.rst))]
              [rng : -e] [env : -ρ] [Γ : -Γ])
            (-x/C -α.x/c)
            )
(define-type -Vs (Listof -V))

(-A . ::= . -Vs
            (-blm [violator : Mon-Party] [origin : Mon-Party] [v : -V] [c : -Vs]))

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

(: V->?e : -V → -?e)
;; Recover value's syntax from evaluated value
(define V->?e
  (match-lambda
    [(-And/C _ (-α.and/c-l (? -e? c₁)) (-α.and/c-r (? -e? c₂))) (-@ 'and/c (list c₁ c₂) -Λ)]
    [(-Or/C  _ (-α.or/c-l  (? -e? c₁)) (-α.or/c-r  (? -e? c₂))) (-@ 'or/c  (list c₁ c₂) -Λ)]
    [(-Not/C (-α.not/c (? -e? c))) (-@ 'not/c (list c) -Λ)]
    [(-Vectorof (-α.vectorof (? -e? c))) (-@ 'vectorof (list c) -Λ)]
    [(-Vector/C (list (-α.vector/c (? -e? cs)) ...)) (-@ 'vector/c (cast cs (Listof -e)) -Λ)]
    [(-St/C _ si (list (-α.struct/c (? -e? cs)) ...)) (-struct/c si (cast cs (Listof -e)) 0)]
    [_ #f]))

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
    [(-Vector/same γ _ α) `(vector/same ,(show-α γ) ▹ ,(show-α α))]
    [(-And/C _ l r) `(and/c ,(show-α l) ,(show-α r))]
    [(-Or/C _ l r) `(or/c ,(show-α l) ,(show-α r))]
    [(-Not/C γ) `(not/c ,(show-α γ))]
    [(-Vectorof γ) `(vectorof ,(show-α γ))]
    [(-Vector/C γs) `(vector/c ,@(map show-α γs))]
    [(-=>i doms rst d ρ Γ)
     (define-values (xs cs)
       (for/lists ([xs : (Listof Symbol)] [cs : (Listof -?e)])
                  ([dom : (Pairof Symbol -α.dom) doms])
         (match-define (cons x (-α.dom c)) dom)
         (values x (and (-e? c) c))))
     (define dep? (not (set-empty? (∩ (FV d) (list->set xs)))))
     (match* (dep? rst)
       [(#f #f)
        `(,@(map show-?e cs) . -> . ,(show-e d))]
       [(#f (cons x* (and γ* (-α.rst c*))))
        `(,(map show-?e cs) #:rest ,(if (-e? c*) (show-e c*) (show-α γ*)) . ->* . ,(show-e d))]
       [(#t #f)
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-?e c)))
              (res ,xs ,(show-e d)))]
       [(#t (cons x* (and γ* (-α.rst c*))))
        `(->i ,(for/list : (Listof Sexp) ([x xs] [c cs])
                 `(,x ,(show-?e c)))
              #:rest (,x* ,(if (-e? c*) (show-e c*) (show-α γ*)))
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
(define -●/Vs : (List -V) (list -●/V))
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
