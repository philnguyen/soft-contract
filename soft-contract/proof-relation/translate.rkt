#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt")

(define SMT-base : (Listof Sexp)
  '(;; Unitype
    (declare-datatypes ()
      ((V ; TODO
        Nil
        (Cons (car V) (cdr V))
        (R (unbox_R Real))
        (B (unbox_B Bool))
        (Clo (arity Int) (id Int)))))
    ;; Result
    (declare-datatypes ()
     ((A
       (Val (unbox_Val V))
       (Blm (blm_pos Int) (blm_src Int))
       None)))
    ;; Primitive predicates
    (define-fun is_false ([x V]) Bool
      (= x (B false)))
    (define-fun is_truish ([x V]) Bool
      (not (is_false x)))
    ;; Encodings of primitives
    (define-fun op.> ((v1 V) (v2 V)) A
      (if (exists ((r1 Real) (r2 Real))
                  (and (= v1 (R r1))
                       (= v2 (R r2))))
          (Val (B (> (unbox_R v1) (unbox_R v2))))
          None))
    ))

;; SMT target language
(define-type Term Sexp)
(define-type Formula Sexp) ; Term of type Bool in SMT
(define-type Assertion (List 'assert Formula))
(define-type Dec-Const (List 'declare-const Symbol 'V))
(define-type Dec-Fun (List 'declare-fun Symbol (Listof 'V) 'V))

(struct Entry ([free-vars : (℘ Symbol)] [facts : (℘ Formula)] [expr : Term]) #:transparent)
(struct App ([ctx : -τ] [params : (Listof Var-Name)]) #:transparent)

(: encode : -M -Γ -e → (Values (Listof Sexp) Sexp))
;; Encode query `M Γ ⊢ e : (✓|✗|?)`,
;; spanning from `Γ, e`, only translate neccessary entries in `M`
(define (encode M Γ e)
  (define-values (refs top-entry) (encode-e ∅eq Γ e))
  (let loop ([fronts : (℘ App) refs]
             [seen : (℘ App) ∅]
             [def-funs : (HashTable App (Listof Entry)) (hash)])
    (cond
      [(set-empty? fronts)
       (emit def-funs top-entry)]
      [else
       (define-values (fronts* seen* def-funs*)
         (for/fold ([fronts* : (℘ App) ∅]
                    [seen* : (℘ App) seen]
                    [def-funs* : (HashTable App (Listof Entry)) (hash)])
                   ([front fronts])
           (match-define (App τ xs) front)
           (define As (hash-ref M τ))
           (define-values (refs entries) (encode-τ τ xs As))
           (define def-funs** (hash-set def-funs* front entries))
           (define-values (fronts** seen**)
             (for/fold ([fronts** : (℘ App) fronts*]
                        [seen** : (℘ App) seen*])
                       ([ref refs] #:unless (∋ seen** ref))
               (values (set-add seen** ref)
                       (set-add fronts** ref))))
           (values fronts** seen** def-funs**)))
       (loop fronts* seen* def-funs*)])))

(: query-try-prove : -M -Γ -e → (Listof Sexp))
(define (query-try-prove M Γ e)
  (define-values (decs goal) (encode M Γ e))
  `(,@decs (assert (is_false ,goal)) (check-sat)))

(: query-try-refute : -M -Γ -e → (Listof Sexp))
(define (query-try-refute M Γ e)
  (define-values (decs goal) (encode M Γ e))
  `(,@decs (assert (is_truish ,goal)) (check-sat)))

(: encode-τ : -τ (Listof Var-Name) (℘ -A) → (Values (℘ App) (Listof Entry)))
(define (encode-τ τ xs As)
  (define-set refs : App)
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
                (Entry free-vars (set-add facts `(= ,tₐₚₚ (Val ,tₐ))) tₐ)]
               [else
                (define-values (refs+ entry) (encode-e bound Γ #|hack|# -ff))
                (refs-union! refs+)
                (match-define (Entry free-vars facts _) entry)
                (define xₐ (fresh-name!))
                (Entry (set-add free-vars xₐ)
                       (set-add facts `(= ,tₐₚₚ (Val ,xₐ)))
                       #|hack|# `(B false))])
             ]
            [(-ΓE Γ (-blm l+ lo _ _))
             (define-values (refs+ entry) (encode-e bound Γ #|hack|# -ff))
             (refs-union! refs+)
             entry]))
      ,(Entry ∅eq {set `(= ,tₐₚₚ None)} #f)))
  
  (values refs cases))

(: encode-e : (℘ Var-Name) -Γ -e → (Values (℘ App) Entry))
(define (encode-e bound Γ e)

  (define-set free-vars : Symbol #:eq? #t)
  (define-set asserts : Formula)
  (define-set refs : App)
  (match-define (-Γ φs _ γs) Γ)

  (define (fresh-free!) : Symbol
    (define x (fresh-name!))
    (free-vars-add! x)
    x)

  (: ⦃app⦄-ok! : -τ -e (Listof Var-Name) (Listof -e) → Term)
  ;; Encode that `eₕ(eₓs)` has succcessfully returned
  (define (⦃app⦄-ok! τ eₕ xs eₓs)
    (define tₕ (⦃e⦄! eₕ))
    (define tₓs (map ⦃e⦄! eₓs))
    (define fₕ (fun-name τ xs))
    (define xₐ (fresh-free!))
    (define arity (length xs))
    (refs-add! (App τ xs))
    (asserts-add! `(exists ((id Int)) (= ,tₕ (Clo ,arity id))))
    (asserts-add! `(= (,fₕ ,@tₓs) (Val ,xₐ)))
    xₐ)

  (: ⦃app⦄-err! : -τ -e (Listof Var-Name) (Listof -e) Mon-Party Mon-Party → Void)
  ;; Encode that `eₕ(eₓs)` has succcessfully returned
  (define (⦃app⦄-err! τ eₕ xs eₓs l+ lo)
    (define tₕ (⦃e⦄! eₕ))
    (define tₓs (map ⦃e⦄! eₓs))
    (define fₕ (fun-name τ xs))
    (define arity (length xs))
    (refs-add! (App τ xs))
    (asserts-add! `(= (,fₕ ,@tₓs) (Blm ,(⦃l⦄ l+) ,(⦃l⦄ lo)))))

  ;; encode the fact that `e` has successfully evaluated
  (define/memo (⦃e⦄! [e : -e]) : Term
    (match e
      [(-b b) (⦃b⦄ b)]
      [(-x x)
       (define t (⦃x⦄ x))
       (cond [(∋ bound x) t]
             [else (free-vars-add! t) t])]
      [(-λ (? list? xs) e)
       (define n (length xs))
       `(Clo ,n ,(next-int!))] ; TODO exists id instead
      [(-@ (? -o? o) es _)
       (define tₒ (⦃o⦄ o))
       (define ts (map ⦃e⦄! es))
       (define xₐ (fresh-free!))
       (asserts-add! `(= (,tₒ ,@ts) (Val ,xₐ)))
       xₐ]
      [(-@ eₕ eₓs _)
       (or
        (for/or : (Option Term) ([γ γs])
          (match-define (-γ τ bnd blm) γ)
          (match-define (-binding φₕ xs x->φ) bnd)
          (cond
            [(and (equal? eₕ (and φₕ (φ->e φₕ)))
                  (for/and : Boolean ([x xs] [eₓ eₓs])
                    (equal? eₓ (hash-ref x->φ x #f))))
             
             (⦃app⦄-ok! τ eₕ xs eₓs)]
            [else #f]))
        (fresh-free!))]
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
    (asserts-add! `(is_truish ,t)))
  (define tₜₒₚ (⦃e⦄! e))

  (values refs (Entry free-vars asserts tₜₒₚ)))

(: emit : (HashTable App (Listof Entry)) Entry → (Values (Listof Sexp) Sexp))
;; Emit base and target to prove/refute
(define (emit def-funs top)
  (match-define (Entry consts facts goal) top)
  
  (define emit-def-funs
    (for/fold ([acc : (Listof Sexp) '()])
              ([(f-xs entries) def-funs])
      (match-define (cons f xs) f-xs)
      (define n (length xs))
      (define tₓs (map ⦃x⦄ xs))
      (define decs
        `((declare-fun ,(make-list n 'V) V)
          (assert (forall ,(for/list : (Listof Sexp) ([x tₓs])
                             `[,x V])
                          (or ,@(for/list ([entry entries])
                                  (match-define (Entry xs facts _) entry)
                                  (define conj
                                    (match (set->list facts)
                                      ['() 'true]
                                      [(list φ) φ]
                                      [φs `(and ,@φs)]))
                                  (cond
                                    [(set-empty? xs) conj]
                                    [else `(exists ,(for/list : (Listof Sexp) ([x xs])
                                                      `(,x V))
                                                   ,conj)])))))))
      (append decs acc)))

  (define emit-dec-consts : (Listof Sexp)
    (for/list ([x consts])
      `(declare-const ,x V)))

  (define emit-asserts : (Listof Sexp)
    (for/list ([φ facts])
      `(assert ,φ)))

  (values (append SMT-base emit-def-funs emit-dec-consts emit-asserts)
          goal))

(: ⦃l⦄ : Mon-Party → Integer)
(define ⦃l⦄
  (let ([m : (HashTable Mon-Party Integer) (make-hash)])
    (λ (l) (hash-ref! m l (λ () (hash-count m))))))

(: ⦃b⦄ : Base → Term)
(define (⦃b⦄ b)
  (match b
    [#f `(B false)]
    [#t `(B true)]
    [(? real? r) `(R ,r)]
    [_ (error '⦃e⦄! "base value: ~a" b)]))

(: ⦃x⦄ : Var-Name → Symbol)
(define ⦃x⦄
  (let ([m : (HashTable Var-Name Symbol) (make-hasheq)])
    (λ (x) ; TODO serious attempt
      (hash-ref! m x
                 (λ ()
                   (cond
                     [(integer? x) (format-symbol "x.~a" x)]
                     [else x]))))))

(: fresh-name! : → Symbol)
(define fresh-name!
  (let ([i : Natural 0])
    (λ ()
      (begin0 (format-symbol "v.~a" i)
        (set! i (+ 1 i))))))

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
    [(? symbol? o) (format-symbol "op.~a" o)]))

(: next-int! : → Natural)
(define next-int!
  (let ([i : Natural 0])
    (λ ()
      (begin0 i (set! i (+ 1 i))))))


(module+ test
  (require typed/rackunit)
  
  (define +x (-x 'x))
  (define +y (-x 'y))
  (query-try-prove ⊥M (Γ+ ⊤Γ (-@ '> (list +x (-b 4)) 0)) (-@ '> (list +x (-b 3)) 0)))

