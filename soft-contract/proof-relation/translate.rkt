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

(: base-datatypes : (℘ Natural) → (Listof Sexp))
(define (base-datatypes arities)
  (define st-defs : (Listof Sexp)
    (for/list ([n arities])
      (define St_k (format-symbol "St_~a" n))
      (define tag_k (format-symbol "tag_~a" n))
      (define fields : (Listof Sexp)
        (for/list ([i n]) `(,(format-symbol "field_~a_~a" n i) V)))
      `(,St_k (,tag_k Int) ,@fields)))
  
  `(;; Unitype
    (declare-datatypes ()
      ((V ; TODO
        Undefined
        Null
        (N [real Real] [imag Real])
        (B [unbox_B Bool])
        (O [op Int])
        (Sym [sym Int])
        (Str [str Int])
        (Op [name Int])
        (Clo [arity Int] [id Int])
        ;; structs with hard-coded arities
        ,@st-defs)))
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

(define hack-for-is_int : (Listof Sexp)
  '{(assert (forall ([x Real] [y Real])
              (=> (and (is_int x) (is_int y)) (is_int (+ x y)))))
    (assert (forall ([x Real] [y Real])
              (=> (and (is_int x) (is_int y)) (is_int (- x y)))))
    (assert (forall ([x Real] [y Real])
              (=> (and (is_int x) (is_int y)) (is_int (* x y)))))
    })

(: SMT-base : (℘ Natural) → (Listof Sexp))
(define (SMT-base struct-arities)
  `(,@(base-datatypes struct-arities)
    ,@base-predicates))

;; SMT target language
(define-type Term Sexp)
(define-type Formula Sexp) ; Term of type Bool in SMT
(struct Entry ([free-vars : (℘ Symbol)] [facts : (Listof Formula)] [expr : Term]) #:transparent)
(struct App ([ctx : -τ] [params : (Listof Var-Name)]) #:transparent)
(struct Res ([ok : (Listof Entry)] [er : (Listof Entry)]) #:transparent)
(Defn-Entry . ::= . -o App)
(define-type Memo-Table
  ;; Memo table maps each function application to a pair of formulas:
  ;; - When the application succeeds
  ;; - When the application goes wrong
  (HashTable App Res))

(: encode : -M -Γ -e → (Values (Listof Sexp) Sexp))
;; Encode query `M Γ ⊢ e : (✓|✗|?)`,
;; spanning from `Γ, e`, only translating neccessary entries in `M`
(define (encode M Γ e)
  (define-values (refs top-entry) (encode-e ∅eq Γ e))
  (let loop ([fronts : (℘ Defn-Entry) refs]
             [seen : (℘ Defn-Entry) refs]
             [def-prims : (℘ (Listof Sexp)) ∅]
             [def-funs : Memo-Table (hash)])
    (cond
      [(set-empty? fronts)
       (define st-arities
         (for/fold ([acc : (℘ Natural) ∅eq])
                   ([entry seen])
           (match entry
             [(or (-st-mk s) (-st-p s) (-st-ac s _) (-st-mut s _)) #:when s
              (set-add acc (-struct-info-arity s))]
             [_ acc])))
       (emit st-arities def-prims def-funs top-entry)]
      [else
       (define-values (fronts* seen* def-prims* def-funs*)
         (for/fold ([fronts* : (℘ Defn-Entry) ∅]
                    [seen* : (℘ Defn-Entry) seen]
                    [def-prims* : (℘ (Listof Sexp)) def-prims]
                    [def-funs* : Memo-Table def-funs])
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

(: encode-τ : -τ (Listof Var-Name) (℘ -A) → (Values (℘ Defn-Entry) Res))
;; Translate memo-table entry `τ(xs) → {A…}` to pair of formulas for when application
;; fails and passes
(define (encode-τ τ xs As)
  (define-set refs : Defn-Entry)
  (define tₓs (map ⦃x⦄ xs))
  (define fₕ (fun-name τ xs))
  (define tₐₚₚ (-tapp fₕ tₓs))
  (define bound (list->set xs))
  
  ;; Accumulate pair of formulas describing conditions for succeeding and erroring
  (define-values (oks ers)
    (for/fold ([oks : (Listof Entry) '()]
               [ers : (Listof Entry) '()])
              ([A As])
      (match A
        [(-ΓW Γ (-W _ sₐ))
         (define eₒₖ
           (cond
             [sₐ
              (define-values (refs+ entry) (encode-e bound Γ sₐ))
              (refs-union! refs+)
              (match-define (Entry free-vars facts tₐₙₛ) entry)
              (Entry free-vars
                     (cons `(= ,tₐₚₚ (Val ,tₐₙₛ))
                           facts)
                     tₐₙₛ)]
             [else
              (define-values (refs+ entry) (encode-e bound Γ #|hack|# -ff))
              (refs-union! refs+)
              (match-define (Entry free-vars facts _) entry)
              (Entry free-vars facts #|hack|# '(B false))]))
         (values (cons eₒₖ oks) ers)]
        [(-ΓE Γ (-blm l+ lo _ _))
         (define eₑᵣ
           (let-values ([(refs+ entry) (encode-e bound Γ #|hack|# -ff)])
             (refs-union! refs+)
             (match-define (Entry free-vars facts _) entry)
             (Entry free-vars
                    (cons `(= ,tₐₚₚ (Blm ,(⦃l⦄ l+) ,(⦃l⦄ lo)))
                          facts)
                    #|hack|# `(B false))))
         (values oks (cons eₑᵣ ers))])))
  
  (values refs (Res oks ers)))

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

  ;; Encode that `eₕ(eₓs)` has succcessfully returned
  (define/memo (⦃app⦄-ok! [τ : -τ] [eₕ : -e] [xs : (Listof Var-Name)] [eₓs : (Listof -e)]) : Term
    (define tₕ (⦃e⦄! eₕ))
    (define tₓs (map ⦃e⦄! eₓs))
    (define fₕ (fun-name τ xs))
    (define xₐ (fresh-free!))
    (define arity (length xs))
    (refs-add! (App τ xs))
    (assert-prop! `(exists ([id Int]) (= ,tₕ (Clo ,arity id))))
    (define tₐₚₚ (-tapp fₕ tₓs))
    (assert-eval! tₐₚₚ `(Val ,xₐ))
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
      [(? -o? o) `(O ,(⦃o⦄ᵥ o))]
      [(-x x)
       (define t (⦃x⦄ x))
       (cond [(∋ bound x) t]
             [else (free-vars-add! t) t])]
      [(-λ (? list? xs) e)
       (define n (length xs))
       (define t (fresh-free!))
       (assert-prop! `(is-Clo ,t))
       (assert-prop! `(= (arity ,t) ,(length xs)))
       t]
      [(-@ (? -o? o) es _)
       (define ts (map ⦃e⦄! es))
       (refs-add! o)
       (cond
         [(o->pred o) => (λ ([f : ((Listof Term) → Term)]) (f ts))]
         [else
          (define xₐ (fresh-free!))
          (assert-eval! (-tapp (⦃o⦄ o) ts) `(Val ,xₐ))
          xₐ])]
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
    (assert-prop! (tsimp (⦃e⦄! (φ->e φ)))))
  (define tₜₒₚ (⦃e⦄! e))

  (values refs (Entry free-vars `(,@(reverse asserts-eval) ,@(reverse asserts-prop)) tₜₒₚ)))

(: emit : (℘ Natural) (℘ (Listof Sexp)) Memo-Table Entry → (Values (Listof Sexp) Sexp))
;; Emit base and target to prove/refute
(define (emit struct-arities def-prims def-funs top)
  (match-define (Entry consts facts goal) top)

  (define emit-hack-for-is_int : (Listof Sexp)
    (cond [(should-include-hack-for-is_int? facts) hack-for-is_int]
          [else '()]))
  
  (define emit-def-prims
    (for/fold ([acc : (Listof Sexp) '()])
              ([def-prim def-prims])
      (append def-prim acc)))
  
  (define-values (emit-dec-funs emit-def-funs)
    (for/fold ([decs : (Listof Sexp) '()]
               [defs : (Listof Sexp) '()])
              ([(f-xs res) def-funs])
      (match-define (App τ xs) f-xs)
      (define n (length xs))
      (define tₓs (map ⦃x⦄ xs))
      (define fₕ (fun-name τ xs))
      (define tₐₚₚ (-tapp fₕ tₓs))
      (match-define (Res oks ers) res)

      (: mk-cond : (Listof Entry) → (Listof Sexp))
      (define (mk-cond entries)
        (for/list ([entry entries])
          (match-define (Entry xs facts _) entry)
          (define conj (-tand facts))
          (cond
            [(set-empty? xs)
             conj]
            [else
             (define exists-xs : (Listof Sexp) (for/list ([x xs]) `(,x V)))
             `(exists ,exists-xs ,conj)])))

      (define ok-conds (mk-cond oks))
      (define er-conds (mk-cond ers))
      (define params : (Listof Sexp) (for/list ([x tₓs]) `(,x V)))

      (: assrt : (Listof Sexp) Sexp → Sexp)
      (define (assrt params cnd)
        `(assert
          ,(cond
             [(null? params) cnd]
             [else `(forall ,params (! ,cnd :pattern ,tₐₚₚ))])))
      
      (values
       (cons `(declare-fun ,fₕ ,(make-list n 'V) A) decs)
       (list*
        ;; For each function, generate implications from returns and blames
        (assrt params `(=> (is-Val ,tₐₚₚ) ,(-tor ok-conds)))
        (assrt params `(=> (is-Blm ,tₐₚₚ) ,(-tor er-conds)))
        defs))))

  (define emit-dec-consts : (Listof Sexp) (for/list ([x consts]) `(declare-const ,x V)))
  (define emit-asserts : (Listof Sexp) (for/list ([φ facts]) `(assert ,φ)))

  (values `(,@(SMT-base struct-arities)
            ,@emit-def-prims
            ,@emit-hack-for-is_int
            ,@emit-dec-funs
            ,@emit-def-funs
            ,@emit-dec-consts
            ,@emit-asserts)
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
    [(? symbol? s) `(Sym ,(⦃sym⦄ s))]
    [(? string? s) `(Str ,(⦃str⦄ s))]
    [(list) `Null]
    [_ (error '⦃e⦄! "base value: ~a" b)]))

(: ⦃𝒾⦄ : -𝒾 → Symbol)
(define (⦃𝒾⦄ 𝒾) (format-symbol "t.~a" (-𝒾-name 𝒾)))

(: ⦃x⦄ : Var-Name → Symbol)
(define (⦃x⦄ x)
  
  (: elim-sub/sup-scripts : String → String)
  (define (elim-sub/sup-scripts s)

    (: subst : Char → (Listof Char))
    (define (subst c)
      (case c
        [(#\₀) '(#\_ #\_ #\0)]
        [(#\₁) '(#\_ #\_ #\1)]
        [(#\₂) '(#\_ #\_ #\2)]
        [(#\₃) '(#\_ #\_ #\3)]
        [(#\₄) '(#\_ #\_ #\4)]
        [(#\₅) '(#\_ #\_ #\5)]
        [(#\₆) '(#\_ #\_ #\6)]
        [(#\₇) '(#\_ #\_ #\7)]
        [(#\₈) '(#\_ #\_ #\8)]
        [(#\₉) '(#\_ #\_ #\9)]
        [(#\⁰) '(#\_ #\^ #\0)]
        [(#\¹) '(#\_ #\^ #\1)]
        [(#\²) '(#\_ #\^ #\2)]
        [(#\³) '(#\_ #\^ #\3)]
        [(#\⁴) '(#\_ #\^ #\4)]
        [(#\⁵) '(#\_ #\^ #\5)]
        [(#\⁶) '(#\_ #\^ #\6)]
        [(#\⁷) '(#\_ #\^ #\7)]
        [(#\⁸) '(#\_ #\^ #\8)]
        [(#\⁹) '(#\_ #\^ #\9)]
        [else (list c)]))

    (list->string (append-map subst (string->list s))))

  (cond [(integer? x) (format-symbol "x.~a" x)]
        [else (string->symbol (elim-sub/sup-scripts (symbol->string x)))]))

(: fun-name : -τ (Listof Var-Name) → Symbol)
(define fun-name
  (let ([m : (HashTable (Pairof (Listof Var-Name) -τ) Symbol) (make-hash)])
    (λ (τ xs)
      (hash-ref! m (cons xs τ) (λ () (format-symbol "f.~a" (hash-count m)))))))

(: ⦃o⦄ : -o → Symbol)
(define (⦃o⦄ o)
  (match o
    [(-st-p s) (st-p-name s)]
    [(-st-mk s) (st-mk-name s)]
    [(-st-ac s i) (st-ac-name s i)]
    [(-st-mut s _) (error '⦃o⦄ "TODO: mutator for ~a" (st-name s))]
    [(? symbol? o)
     (format-symbol "o.~a" (string-replace (symbol->string o) "?" "_huh"))]))

(: ⦃o⦄ᵥ : -o → Integer)
(define ⦃o⦄ᵥ
  (let ([m : (HashTable -o Integer) (make-hash)])
    (λ (o) (hash-ref! m o (λ () (hash-count m))))))

(define ⦃sym⦄ : (Symbol → Integer)
  (let ([m : (HashTable Symbol Integer) (make-hasheq)])
    (λ (s) (hash-ref! m s (λ () (hash-count m))))))

(define ⦃str⦄ : (String → Integer)
  (let ([m : (HashTable String Integer) (make-hash)])
    (λ (s) (hash-ref! m s (λ () (hash-count m))))))

(: o->pred : -o → (Option ((Listof Term) → Term)))
(define (o->pred o)
  (case o
    [(defined?)
     (λ ([ts : (Listof Term)])
       `(B (not (is-Undefined ,@ts))))]
    [(number?)
     (λ ([ts : (Listof Term)])
       `(B (is-N ,@ts)))]
    [(real?)
     (λ ([ts : (Listof Term)])
       `(B (is-R ,@ts)))]
    [(integer?)
     (λ ([ts : (Listof Term)])
       `(B (is-Z ,@ts)))]
    [(symbol?)
     (λ ([ts : (Listof Term)])
       `(B (is-Sym ,@ts)))]
    [(string?)
     (λ ([ts : (Listof Term)])
       `(B (is-Str ,@ts)))]
    [(procedure?)
     (λ ([ts : (Listof Term)]) ; FIXME: prims also
       `(B (is-Clo ,@ts)))]
    [(equal?)
     (λ ([ts : (Listof Term)])
       `(B (= ,@ts)))]
    [(not false?)
     (λ ([ts : (Listof Term)])
       (match ts
         [(list `(B (is_false ,t))) `(B (is_truish ,t))]
         [(list `(B (is_truish ,t))) `(B (is_false ,t))]
         [ts `(B (is_false ,@ts))]))]
    [else
     (match o
       [(-st-p s)
        (match-define (-struct-info 𝒾 n _) s)
        (define p (format-symbol "is-St_~a" n))
        (define tag (format-symbol "tag_~a" n))
        (λ ([ts : (Listof Term)])
          `(B (and (,p ,@ts) (= (,tag ,@ts) ,(⦃struct-info⦄ s)))))]
       [_ #f])]))

(: def-o : -o → (Listof Sexp))
(define (def-o o)
  (case o
    [(defined?)
     '{(define-fun o.defined? ([x V]) A
         (Val (B (not (= x Undefined)))))}]
    [(not false?)
     '{(define-fun o.not ([x V]) A
         (Val (B (= x (B false)))))}]
    [(add1)
     '{(define-fun o.add1 ([x V]) A
         (if (is-N x)
             (Val (N (+ 1 (real x)) (imag x)))
             None))}]
    [(sub1)
     '{(define-fun o.add1 ([x V]) A
         (if (is-N x)
             (Val (N (- (real x) 1) (imag x)))
             None))}]
    [(+)
     '{(define-fun o.+ ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (N (+ (real x) (real y))
                     (+ (imag x) (imag y))))
             None))}]
    [(-)
     '{(define-fun o.- ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (N (- (real x) (real y))
                     (- (imag x) (imag y))))
             None))}]
    [(*)
     '{(define-fun o.* ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (Val (N (- (* (real x) (real y))
                        (* (imag x) (imag y)))
                     (+ (* (real x) (imag y))
                        (* (imag x) (real y)))))
             None))}]
    [(/)
     '{(define-fun o./ ([x V] [y V]) A
         (if (and (is-N x) (is-N y))
             (let ((a (real x))
                   (b (imag x))
                   (c (real y))
                   (d (imag y)))
               (let ((ccdd (+ (* c c) (* d d))))
                 (if (= ccdd 0)
                   None
                   (Val (N (/ (+ (* a c) (* b d)) ccdd)
                           (/ (- (* b c) (* a d)) ccdd))))))
             None))}]
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
    [(symbol?)
     '{(define-fun o.symbol_huh ([x V]) A (Val (B (is-Sym x))))}]
    [(string?)
     '{(define-fun o.string_huh ([x V]) A (Val (B (is-Str x))))}]
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
    [(string-length)
     '{(declare-fun o.string-length (V) A)
       (assert (forall ([x V])
                       (! (iff (is-Str x)
                               (exists ([n Int])
                                       (and (= (o.string-length x) (Val (N n 0)))
                                            (>= n 0))))
                          :pattern (o.string-length x))))
       (assert (forall ([x V])
                       (! (iff (not (is-Str x)) (= (o.string-length x) None))
                          :pattern (o.string-length x))))}]
    [else
     (match o
       [(-st-p s)
        (match-define (-struct-info _ n _) s)
        (define is-St (format-symbol "is-St_~a" n))
        (define tag (format-symbol "tag_~a" n))
        `{(define-fun ,(st-p-name s) ((x V)) A
            (Val (B (and (,is-St x) (= (,tag x) ,(⦃struct-info⦄ s))))))}]
       [(-st-mk s)
        (match-define (-struct-info _ n _) s)
        (define-values (decs xs)
          (for/lists ([decs : (Listof Sexp)] [xs : (Listof Symbol)])
                     ([i n])
            (define x (format-symbol "x~a" i))
            (values `(,x V) x)))
        (define St (format-symbol "St_~a" n))
        `{(define-fun ,(st-mk-name s) ,decs A
            (Val (,St ,(⦃struct-info⦄ s) ,@xs)))}]
       [(-st-ac s i)
        (match-define (-struct-info _ n _) s)
        (define is-St (format-symbol "is-St_~a" n))
        (define field (format-symbol "field_~a_~a" n i))
        (define tag (format-symbol "tag_~a" n))
        `{(define-fun ,(st-ac-name s i) ((x V)) A
            (if (and (,is-St x) (= (,tag x) ,(⦃struct-info⦄ s)))
                (Val (,field x))
                None))}]
       [(-st-mut s _)
        (error 'def-o "mutator for ~a" (st-name s))]
       [_
        (raise (exn:scv:smt:unsupported (format "Unsupported: ~a" o) (current-continuation-marks)))])]))

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

(: should-include-hack-for-is_int? : (Listof Sexp) → Boolean)
(define (should-include-hack-for-is_int? φs)
  (and (has-op? φs 'o.integer_huh)
       (for/or : Boolean ([o (in-list '(o.+ o.- o.*))])
         (has-op? φs o))))

(: has-op? : (Listof Sexp) Symbol → Boolean)
(define (has-op? φs o)

  (define go : (Sexp → Boolean)
    (match-lambda
      [(cons h t) (or (go h) (go t))]
      [s (equal? s o)]))

  (ormap go φs))

(:* -tand -tor : (Listof Term) → Term)
(define -tand
  (match-lambda
    ['() 'true]
    [(list x) x]
    [xs `(and ,@xs)]))
(define -tor
  (match-lambda
    ['() 'false]
    [(list x) x]
    [xs `(or ,@xs)]))

(: -tapp : Term (Listof Term) → Term)
(define (-tapp f xs) (if (null? xs) f `(,f ,@xs)))

(: tsimp : Term → Sexp)
(define (tsimp t)
  (match t
    [`(B (is_false (B ,φ))) `(not ,φ)]
    [`(B (is_truish (B ,φ))) φ]
    [`(B ,φ) φ]
    [_ `(is_truish ,t)]))

(define (st-name [s : -struct-info]) : Symbol (-𝒾-name (-struct-info-id s)))
(define (st-p-name [s : -struct-info]) : Symbol (format-symbol "st.~a?" (st-name s)))
(define (st-mk-name [s : -struct-info]) : Symbol (format-symbol "st.~a" (st-name s)))
(define (st-ac-name [s : -struct-info] [i : Natural]) : Symbol (format-symbol "st.~a_~a" (st-name s) i))

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
