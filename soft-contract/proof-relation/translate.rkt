#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/string
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt")

(struct exn:scv:smt:unsupported exn () #:transparent)

(define base-datatypes : (Listof Sexp)
  '(;; Unitype
    (declare-datatypes ()
      ((V ; TODO
        Null
        (N [real Real] [imag Real])
        (B [unbox_B Bool])
        (Op [name Int])
        (Clo [arity Int] [id Int])
        ;; structs with hard-coded arities
        #;(St [tag Int] [fields Int] [content (Array Int V)]))))
    ;; Result
    (declare-datatypes ()
     ((A
       (Val (unbox_Val V))
       (Blm (blm_pos Int) (blm_src Int))
       None)))
    ))

(define base-predicates : (Listof Sexp)
  '(;; Primitive predicates
    (define-fun is_false ([x V]) Bool
      (= x (B false)))
    (define-fun is_truish ([x V]) Bool
      (not (is_false x)))
    (define-fun is_proc ([x V]) Bool
      (or (exists ((n Int)) (= x (Op n)))
          (exists ((n Int) (id Int)) (= x (Clo n id)))))
    (define-fun has_arity ((x V) (n Int)) Bool
      ;; TODO primitives too
      (exists ((id Int)) (= x (Clo n id))))
    (define-fun is-R ([x V]) Bool
      (and (is-N x) (= 0 (imag x))))
    (define-fun is-Z ([x V]) Bool
      (and (is-R x) (is_int (real x))))
    ))

(define SMT-base : (Listof Sexp)
  `(,@base-datatypes
    ,@base-predicates))

;; SMT target language
(define-type Term Sexp)
(define-type Formula Sexp) ; Term of type Bool in SMT
(struct Entry ([free-vars : (℘ Symbol)] [facts : (Listof Formula)] [expr : Term]) #:transparent)
(struct App ([ctx : -τ] [params : (Listof Var-Name)]) #:transparent)
(Defn-Entry . ::= . -o App)

(: encode : -M -Γ -e → (Values (Listof Sexp) Sexp))
;; Encode query `M Γ ⊢ e : (✓|✗|?)`,
;; spanning from `Γ, e`, only translating neccessary entries in `M`
(define (encode M Γ e)
  (define-values (refs top-entry) (encode-e ∅eq Γ e))
  (let loop ([fronts : (℘ Defn-Entry) refs]
             [seen : (℘ Defn-Entry) ∅]
             [def-prims : (℘ (Listof Sexp)) ∅]
             [def-funs : (HashTable App (Listof Entry)) (hash)])
    (cond
      [(set-empty? fronts)
       (emit def-prims def-funs top-entry)]
      [else
       (define-values (fronts* seen* def-prims* def-funs*)
         (for/fold ([fronts* : (℘ Defn-Entry) ∅]
                    [seen* : (℘ Defn-Entry) seen]
                    [def-prims* : (℘ (Listof Sexp)) def-prims]
                    [def-funs* : (HashTable App (Listof Entry)) def-funs])
                   ([front fronts])
           (define-values (def-prims** def-funs** refs+)
             (match front
               [(App τ xs)
                (define As (hash-ref M τ))
                (define-values (refs entries) (encode-τ τ xs As))
                (values def-prims* (hash-set def-funs* front entries) refs)]
               [(? -o? o)
                (values (set-add def-prims* (def-o o)) def-funs* ∅)]))
           
           (define-values (fronts** seen**)
             (for/fold ([fronts** : (℘ Defn-Entry) fronts*]
                        [seen** : (℘ Defn-Entry) seen*])
                       ([ref refs+] #:unless (∋ seen** ref))
               (values (set-add fronts** ref)
                       (set-add seen** ref))))
           (values fronts** seen** def-prims** def-funs**)))
       (loop fronts* seen* def-prims* def-funs*)])))

(: query-try-prove : -M -Γ -e → (Listof Sexp))
;; Generate formulas whose `unsat`ness implies `M Γ ⊢ e : ✓`
(define (query-try-prove M Γ e)
  (define-values (decs goal) (encode M Γ e))
  `(,@decs (assert (is_false ,goal)) (check-sat)))

(: query-try-refute : -M -Γ -e → (Listof Sexp))
;; Generate formulas whose `unsat`ness implies `M Γ ⊢ e : ✗`
(define (query-try-refute M Γ e)
  (define-values (decs goal) (encode M Γ e))
  `(,@decs (assert (is_truish ,goal)) (check-sat)))

(: encode-τ : -τ (Listof Var-Name) (℘ -A) → (Values (℘ Defn-Entry) (Listof Entry)))
(define (encode-τ τ xs As)
  (define-set refs : Defn-Entry)
  (define tₓs (map ⦃x⦄ xs))
  (define fₕ (fun-name τ xs))
  (define tₐₚₚ `(,fₕ ,@tₓs))
  (define bound (list->set xs))
  
  (define cases : (Listof Entry)
    `(,@(for/list : (Listof Entry) ([A As])
          (match A
            [(-ΓW Γ (-W _ sₐ))
             (cond
               [sₐ
                (define-values (refs+ entry) (encode-e bound Γ sₐ))
                (refs-union! refs+)
                (match-define (Entry free-vars facts tₐ) entry)
                (Entry free-vars (cons `(= ,tₐₚₚ (Val ,tₐ)) facts) tₐ)]
               [else
                (define-values (refs+ entry) (encode-e bound Γ #|hack|# -ff))
                (refs-union! refs+)
                (match-define (Entry free-vars facts _) entry)
                (Entry (set-add free-vars 'i.ans)
                       (cons `(= ,tₐₚₚ (Val i.ans)) facts)
                       #|hack|# `(B false))])
             ]
            [(-ΓE Γ (-blm l+ lo _ _))
             (define-values (refs+ entry) (encode-e bound Γ #|hack|# -ff))
             (refs-union! refs+)
             (match-define (Entry free-vars facts _) entry)
             (Entry free-vars
                    (cons `(= ,tₐₚₚ (Blm ,(⦃l⦄ l+) ,(⦃l⦄ lo))) facts)
                    #|hack|# `(B false))]))
      ,(Entry ∅eq `{ (= ,tₐₚₚ None) } #f)))
  
  (values refs cases))

(: encode-e : (℘ Var-Name) -Γ -e → (Values (℘ Defn-Entry) Entry))
;; Encode pathcondition `Γ` and expression `e`,
(define (encode-e bound Γ e)

  (define-set free-vars : Symbol #:eq? #t)
  (define asserts-eval : (Listof Formula) '())
  (define asserts-prop : (Listof Formula) '())
  (define-set refs : Defn-Entry)
  (match-define (-Γ φs _ γs) Γ)

  (define fresh-free! : (→ Symbol)
    (let ([i : Natural 0])
      (λ ()
        (define x (format-symbol "i.~a" i))
        (set! i (+ 1 i))
        (free-vars-add! x)
        x)))

  (define (assert-eval! [t : Term] [a : Term]) : Void
    (set! asserts-eval (cons `(= ,t ,a) asserts-eval)))

  (define (assert-prop! [φ : Formula]) : Void
    (set! asserts-prop (cons φ asserts-prop)))

  (: ⦃app⦄-ok! : -τ -e (Listof Var-Name) (Listof -e) → Term)
  ;; Encode that `eₕ(eₓs)` has succcessfully returned
  (define (⦃app⦄-ok! τ eₕ xs eₓs)
    (define tₕ (⦃e⦄! eₕ))
    (define tₓs (map ⦃e⦄! eₓs))
    (define fₕ (fun-name τ xs))
    (define xₐ (fresh-free!))
    (define arity (length xs))
    (refs-add! (App τ xs))
    (assert-prop! `(exists ([id Int]) (= ,tₕ (Clo ,arity id))))
    (assert-eval! `(,fₕ ,@tₓs) `(Val ,xₐ))
    xₐ)

  (: ⦃app⦄-err! : -τ -e (Listof Var-Name) (Listof -e) Mon-Party Mon-Party → Void)
  ;; Encode that `eₕ(eₓs)` has succcessfully returned
  (define (⦃app⦄-err! τ eₕ xs eₓs l+ lo)
    (define tₕ (⦃e⦄! eₕ))
    (define tₓs (map ⦃e⦄! eₓs))
    (define fₕ (fun-name τ xs))
    (define arity (length xs))
    (refs-add! (App τ xs))
    (assert-eval! `(,fₕ ,@tₓs) `(Blm ,(⦃l⦄ l+) ,(⦃l⦄ lo))))

  ;; encode the fact that `e` has successfully evaluated
  (define/memo (⦃e⦄! [e : -e]) : Term
    ;(printf "⦃e⦄!: ~a~n" (show-e e))
    (match e
      [(-b b) (⦃b⦄ b)]
      [(? -𝒾? 𝒾)
       (define t (⦃𝒾⦄ 𝒾))
       (free-vars-add! t)
       t]
      [(-x x)
       (define t (⦃x⦄ x))
       (cond [(∋ bound x) t]
             [else (free-vars-add! t) t])]
      [(-λ (? list? xs) e)
       (define n (length xs))
       `(Clo ,n ,(next-int!))] ; TODO exists id instead
      [(-@ (? -o? o) es _)
       (refs-add! o)
       (define tₒ (⦃o⦄ o))
       (define ts (map ⦃e⦄! es))
       (define xₐ (fresh-free!))
       (assert-eval! `(,tₒ ,@ts) `(Val ,xₐ))
       xₐ]
      [(-@ eₕ eₓs _)
       (or
        (for/or : (Option Term) ([γ γs])
          (match-define (-γ τ bnd blm) γ)
          (match-define (-binding φₕ xs x->φ) bnd)
          (cond [(equal? e (binding->s bnd))
                 (⦃app⦄-ok! τ eₕ xs eₓs)]
                [else #f]))
        (begin
          #;(printf "Can't find tail for ~a among ~a~n"
                  (show-e e)
                  (for/list : (Listof Sexp) ([γ γs])
                    (match-define (-γ _ bnd _) γ)
                    (show-s (binding->s bnd))))
          (fresh-free!)))]
      [_ (error '⦃e⦄! "unhandled: ~a" (show-e e))]))

  (: ⦃γ⦄! : -γ → Void)
  (define (⦃γ⦄! γ)
    (match-define (-γ τ bnd blm) γ)
    (define eₐₚₚ (binding->s bnd))
    (when eₐₚₚ
      (match-define (-binding _ xs _) bnd)
      (match-define (-@ eₕ eₓs _) eₐₚₚ)
      (match blm
        [(cons l+ lo) (⦃app⦄-err! τ eₕ xs eₓs l+ lo)]
        [_      (void (⦃app⦄-ok! τ eₕ xs eₓs))])))

  (for ([γ (reverse γs)]) (⦃γ⦄! γ))
  (for ([φ φs])
    (define t (⦃e⦄! (φ->e φ)))
    (assert-prop! `(is_truish ,t)))
  (define tₜₒₚ (⦃e⦄! e))

  (values refs (Entry free-vars `(,@asserts-eval ,@asserts-prop) tₜₒₚ)))

(: emit : (℘ (Listof Sexp)) (HashTable App (Listof Entry)) Entry → (Values (Listof Sexp) Sexp))
;; Emit base and target to prove/refute
(define (emit def-prims def-funs top)
  (match-define (Entry consts facts goal) top)

  (define emit-def-prims
    (for/fold ([acc : (Listof Sexp) '()])
              ([def-prim def-prims])
      (append def-prim acc)))
  
  (define emit-def-funs
    (for/fold ([acc : (Listof Sexp) '()])
              ([(f-xs entries) def-funs])
      (match-define (App τ xs) f-xs)
      (define n (length xs))
      (define tₓs (map ⦃x⦄ xs))
      (define fₕ (fun-name τ xs))
      (define decs
        `((declare-fun ,fₕ ,(make-list n 'V) A)
          (assert (forall ,(for/list : (Listof Sexp) ([x tₓs])
                             `[,x V])
                          (or ,@(for/list : (Listof Formula) ([entry entries])
                                  (match-define (Entry xs facts _) entry)
                                  (define conj
                                    (match facts
                                      ['() 'true]
                                      [(list φ) φ]
                                      [φs `(and ,@φs)]))
                                  (cond
                                    [(set-empty? xs) conj]
                                    [else `(exists ,(for/list : (Listof Sexp) ([x xs])
                                                      `(,x V))
                                                   ,conj)])))))))
      (append decs acc)))

  (define emit-dec-consts : (Listof Sexp) (for/list ([x consts]) `(declare-const ,x V)))
  (define emit-asserts : (Listof Sexp) (for/list ([φ facts]) `(assert ,φ)))

  (values `(,@SMT-base ,@emit-def-prims ,@emit-def-funs ,@emit-dec-consts ,@emit-asserts)
          goal))

(: ⦃l⦄ : Mon-Party → Natural)
(define ⦃l⦄
  (let-values ([(l->nat _₁ _₂) ((inst unique-nat Mon-Party))])
    l->nat))

(: ⦃struct-info⦄ : -struct-info → Natural)
(define ⦃struct-info⦄
  (let-values ([(si->nat _₁ _₂) ((inst unique-nat -struct-info))])
    si->nat))

(: ⦃b⦄ : Base → Term)
(define (⦃b⦄ b)
  (match b
    [#f `(B false)]
    [#t `(B true)]
    [(? number? x) `(N ,(real-part x) ,(imag-part x))]
    [_ (error '⦃e⦄! "base value: ~a" b)]))

(: ⦃𝒾⦄ : -𝒾 → Symbol)
(define (⦃𝒾⦄ 𝒾) (format-symbol "t.~a" (-𝒾-name 𝒾)))

(: ⦃x⦄ : Var-Name → Symbol)
(define (⦃x⦄ x)
  (cond [(integer? x) (format-symbol "x.~a" x)]
        [else x]))

(: fun-name : -τ (Listof Var-Name) → Symbol)
(define fun-name
  (let ([m : (HashTable (Pairof (Listof Var-Name) -τ) Symbol) (make-hash)])
    (λ (τ xs)
      (hash-ref! m (cons xs τ) (λ () (format-symbol "f.~a" (hash-count m)))))))

(: ⦃o⦄ : -o → Symbol)
(define (⦃o⦄ o)
  (match o
    [(-st-p s) (error "TODO")]
    [(-st-mk s) (error "TODO")]
    [(-st-ac s _) (error "TODO")]
    [(-st-mut s _) (error "TODO")]
    [(? symbol? o)
     (format-symbol "o.~a" (string-replace (symbol->string o) "?" "_huh"))]))

(: def-o : -o → (Listof Sexp))
(define (def-o o)
  (case o
    [(not false?)
     '{(define-fun o.not ([x V]) A
         (Val (B (not (= x (B false))))))}]
    [(+)
     '{(define-fun o.+ ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (N (+ (real x) (real y))
                     (+ (imag x) (imag y))))
             None))
       (assert (forall ([x Real] [y Real])
                 (=> (and (is_int x) (is_int y)) (is_int (+ x y)))))}]
    [(-)
     '{(define-fun o.- ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (N (- (real x) (real y))
                     (- (imag x) (imag y))))
             None))
       (assert (forall ([x Real] [y Real])
                 (=> (and (is_int x) (is_int y)) (is_int (- x y)))))}]
    [(*)
     '{(define-fun o.* ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (N (- (* (real x) (real y))
                        (* (imag x) (imag y)))
                     (+ (* (real x) (imag y))
                        (* (imag x) (real y)))))
             None))
       (assert (forall ([x Real] [y Real])
                 (=> (and (is_int x) (is_int y)) (is_int (* x y)))))}]
    [(=)
     '{(define-fun o.= ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (B (= x y)))
             None))}]
    [(> < >= <=) (lift-ℝ²-𝔹 (assert o symbol?))]
    [(equal?)
     '{(define-fun o.equal_huh ([x V] [y V]) A
         (Val (B (= x y))))}]
    [(integer?)
     '{(define-fun o.integer_huh ([x V]) A (Val (B (is-Z x))))}]
    [(real?)
     '{(define-fun o.real_huh ([x V]) A (Val (B (is-R x))))}]
    [(number?) ; TODO
     '{(define-fun o.number_huh ([x V]) A (Val (B (is-N x))))}]
    [(null? empty?)
     '{(define-fun o.null_huh ([x V]) A
         (Val (B (= x Null))))}]
    [(procedure?)
     '{(define-fun o.procedure_huh ([x V]) A
         (Val (B (or (is-Op x) (is-Clo x)))))}]
    [(arity-includes?)
     '{(define-fun o.arity-includes_huh ([a V] [i V]) A
         (if (and (#|TODO|# is-Z a) (is-Z i))
             (Val (B (= a i)))
             None))}]
    [(procedure-arity)
     '{(define-fun o.procedure-arity ([x V]) A
         (if (is-Clo x)
             (Val (N (arity x) 0))
             None))}]
    [else (raise (exn:scv:smt:unsupported (format "Unsupported: ~a" o) (current-continuation-marks)))]))

(: lift-ℝ²-𝔹 : Symbol → (Listof Sexp))
(define (lift-ℝ²-𝔹 o)
  (define name (⦃o⦄ o))
  `{(define-fun ,name ([x V] [y V]) A
      (if (and (is-R x) (is-R y))
          (Val (B (,o (real x) (real y))))
          None))})

(: next-int! : → Natural)
(define next-int!
  (let ([i : Natural 0])
    (λ ()
      (begin0 i (set! i (+ 1 i))))))


(module+ test
  (require typed/rackunit)
  
  (define +x (-x 'x))
  (define +y (-x 'y))
  (define +z (-x 'z))
  (encode ⊥M
           (Γ+ ⊤Γ
                (-@ 'integer? (list +x) 0)
                (-@ 'integer? (list +y) 0)
                (-@ '= (list +z (-@ '+ (list +x +y) 0)) 0))
           (-@ 'integer? (list +z) 0)))
