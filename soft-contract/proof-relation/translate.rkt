#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base)
         racket/match
         racket/set
         racket/string
         syntax/parse/define
         z3/smt
         racket/list
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt")

(struct exn:scv:unsupported exn () #:transparent)
(define-type →Z3-Ast (→ Z3-Ast))
(define-type →Void   (→ Void))

;; This table is just for printing out each warning once
(define unsupported : (HashTable Any Void) (make-hash))

(struct Entry ([free-vars : (℘ Symbol)]
               [facts     : (℘ →Z3-Ast)]
               [expr      : →Z3-Ast])
  #:transparent)
(struct App ([ctx : -αₖ] [fvs : (Listof Symbol)]) #:transparent)
(struct Res ([ok : (Listof Entry)] [er : (Listof Entry)]) #:transparent)
(define-type App-Trace (℘ App))
;; Translation context for application includes the application and history of calls
;; that result in it
(struct App-Ctx ([app : App] [ctx : App-Trace]) #:transparent)
(Defn-Entry . ::= . -o App-Ctx)
(define-type Memo-Table
  ;; Memo table maps each function application to a pair of formulas:
  ;; - When application succeeds
  ;; - When application goes wrong
  (HashTable App Res))

(: encode : (HashTable -αₖ (℘ -ΓA)) -Γ -e → (Values →Void →Z3-Ast))
;; Encode `M Γ ⊢ e` into a pair of thunks that emit assertions and goal to check for
;; satisfiability
(define (encode M Γ e)
  (define-values (refs top-entry) (encode-e ∅ ∅eq Γ e))
  
  (define-set seen-defns : App-Ctx #:as-mutable-hash? #t)
  (define-set seen-prims : -o)
  (define def-funs : Memo-Table (make-hash))

  (: touch! : Defn-Entry → Void)
  (define (touch! defn-entry)
    (match defn-entry
      [(and app-ctx (App-Ctx (and app (App αₖ _)) _))
       (unless (seen-defns-has? app-ctx)
         (seen-defns-add! app-ctx)
         (define As (hash-ref M αₖ))
         (define-values (refs entries) (encode-App-Ctx app-ctx As))
         (hash-set! def-funs app entries)
         (set-for-each refs touch!))]
      [(? -o? o)
       (seen-prims-add! o)]))

  (set-for-each refs touch!)
  (emit seen-prims def-funs top-entry))

(: encode-App-Ctx : App-Ctx (℘ -ΓA) → (Values (℘ Defn-Entry) Res))
;; Translate memo-table entry `αₖ(xs) → {A…}` to pair of formulas for when application
;; fails and passes
(define (encode-App-Ctx app-ctx ΓAs)
  (define-set refs : Defn-Entry)
  (match-define (App-Ctx app ctx) app-ctx)
  (match-define (App αₖ fvs) app)
  (define ⦃fv⦄s (map ⦃x⦄ fvs))
  (define xs : (Listof Symbol)
    (match αₖ
      [(-ℬ xs _ _) 
       (cond
         [(list? xs) xs]
         [else
          (hash-ref! unsupported αₖ (λ () (log-warning "unsupported: ~a~n" (show-αₖ αₖ))))
          '()])]
      [(-ℳ x _ _ _ _) (list x)]
      [(-ℱ x _ _ _ _) (list x)]))
  (define tₓs : (Listof →Z3-Ast)
    (for/list ([x xs])
      (define t (⦃x⦄ x))
      (λ () (val-of t))))
  (define fₕ (fun-name app))
  (define tₐₚₚ (-tapp fₕ ⦃fv⦄s tₓs))
  (define bound (∪ (list->seteq fvs) (list->seteq xs)))

  ;; Accumulate pair of formulas describing conditions for succeeding and erroring
  (define-values (oks ers)
    (for/fold ([oks : (Listof Entry) '()]
               [ers : (Listof Entry) '()])
              ([ΓA ΓAs])
      (match-define (-ΓA Γ A) ΓA)
      (match A
        [(-W Vₐs sₐ)
         (define eₒₖ
           (cond
             [sₐ
              (define-values (refs+ entry) (encode-e ctx bound Γ sₐ))
              (refs-union! refs+)
              (match-define (Entry free-vars facts tₐₙₛ) entry)
              (define facts*
                (match Vₐs
                  [(-b b) {seteq (λ () (=/s (tₐₙₛ) (⦃b⦄ b)))}]
                  [(-● ps)
                   (for/seteq: : (℘ →Z3:Ast) ([p ps])
                     (λ () (⦃p⦄ p (tₐₙₛ))))]
                  [_ ∅eq]))
              (Entry free-vars
                     (set-add (∪ facts facts*) (λ () (=/s (tₐₚₚ) (@/s 'Val (tₐₙₛ)))))
                     tₐₙₛ)]
             [else
              (define-values (refs+ entry) (encode-e ctx bound Γ #|HACK|# -ff))
              (refs-union! refs+)
              (match-define (Entry free-vars facts _) entry)
              (define facts*
                (match Vₐs
                  [(-b b) {seteq (λ () (=/s (@/s 'unbox_Val (tₐₚₚ)) (⦃b⦄ b)))}]
                  [(-● ps)
                   (for/seteq: : (℘ →Z3:Ast) ([p ps])
                     (λ () (⦃p⦄ p (@/s 'unbox_Val (tₐₚₚ)))))]
                  [_ ∅eq]))
              (Entry free-vars
                     (∪ facts facts*)
                     #|hack|# (λ () (@/s 'B false/s)))]))
         (values (cons eₒₖ oks) ers)]
        [(-blm l+ lo _ _ _)
         (define eₑᵣ
           (let-values ([(refs+ entry) (encode-e ctx bound Γ #|hack|# -ff)])
             (refs-union! refs+)
             (match-define (Entry free-vars facts _) entry)
             (Entry free-vars
                    (set-add facts (λ () (=/s (tₐₚₚ) (@/s 'Blm (-l->-⦃l⦄ l+) (-l->-⦃l⦄ lo)))))
                    #|HACK|# (λ () (@/s 'B false/s)))))
         (values oks (cons eₑᵣ ers))])))
  (values refs (Res oks ers)))

(: encode-e : App-Trace (℘ Symbol) -Γ -e → (Values (℘ Defn-Entry) Entry))
;; Encode path-condition `Γ` and expression `e` into a
;; - a Z3-Ast-producing thunk, and
;; - a set of function definitions to encode
(define (encode-e trace bound Γ e)
  
  (define-set free-vars : Symbol  #:eq? #t)
  (define-set props     : →Z3-Ast #:eq? #t)
  (define asserts-app : (HashTable →Z3-Ast (U #t ; is-Val
                                              Symbol ; is-Val + instantiate
                                              (Pairof Integer Integer) ; blm
                                              ))
    (make-hash))
  (define-set refs : Defn-Entry)
  (match-define (-Γ φs _ γs) Γ)

  (define fresh-free! : (Symbol → Symbol)
    (let ([m : (HashTable Symbol Natural) (make-hasheq)])
      (λ (s)
        (hash-update! m s add1 (λ () 0))
        (define i (hash-ref m s))
        (define x (format-symbol "~a.~a" s i))
        (free-vars-add! x)
        x)))

  (define app-term! : (→Z3-Ast → →Z3-Ast)
    (let ([m : (HashTable →Z3-Ast →Z3-Ast) (make-hasheq)])
      (λ (tₐₚₚ)
        (hash-ref! m tₐₚₚ
                   (λ ()
                     (define tₐ (format-symbol "a.~a" (hash-count m)))
                     (free-vars-add! tₐ)
                     (hash-set! asserts-app tₐₚₚ tₐ)
                     (λ () (val-of tₐ)))))))

  ;; Add a reminder to encode memo table entries for `αₖ` as a 1st-order function
  (define/memo (⦃fun⦄! [eₕ : -e] [app : App]) : Symbol
     (⦃e⦄! eₕ) ; for "side-effect" of `eₕ` having evaluated
     (refs-add! (App-Ctx app (set-add trace app)))
     (fun-name app))

  ;; encode application
  (define/memo (⦃app⦄!
                [αₖ : -αₖ]
                [eₕ : -e]
                [fvs : (Listof Symbol)]
                [eₓs : (Listof -e)]) : →Z3-Ast
    (define app (App αₖ fvs))
    (cond
      ;; If this is a recursive application, just existentialize the result for now,
      ;; because encoding of recursive functions slows down Z3 for sat/unknown queries
      [(∋ trace app)
       (define t (fresh-free! 'rec-app))
       ;(printf "Existentializing recursive app~n")
       (λ () (@/s 'Val (val-of t)))]
      [else
       (define f (⦃fun⦄! eₕ app))
       (define ⦃fvs⦄ (map ⦃x⦄ fvs))
       (define ⦃eₓs⦄ (map ⦃e⦄! eₓs))
       (-tapp f ⦃fvs⦄ ⦃eₓs⦄)]))
  
  ;; encode that `e` has successfully evaluated
  (define/memo (⦃e⦄! [e : -e]) : →Z3-Ast
    (match e
      [(-b b) (λ () (⦃b⦄ b))]
      [(? -𝒾? 𝒾)
       (define t (⦃𝒾⦄ 𝒾))
       (free-vars-add! t)
       (λ () (val-of t))]
      [(? -o? o)
       (define id (-o->-⦃o⦄ o))
       (λ () (@/s 'Proc id))]
      [(-x x)
       (define t (⦃x⦄ x))
       (unless (∋ bound x)
         (free-vars-add! t))
       (λ () (val-of t))]
      [(-λ xs e)
       (define t (fresh-free! 'lam))
       (props-add! (λ () (@/s 'is-Proc t)))
       (cond
         [(list? xs) (props-add! (λ () (=/s (@/s 'arity t) (length xs))))]
         [else (log-warning "No precise translation for varargs")])
       (λ () (val-of t))]

      ;; Hacks for special applications go here
      [(-@ (-@ 'and/c ps _) es _)
       (define ts : (Listof →Z3-Ast) (for/list ([p ps]) (⦃e⦄! (-@ p es +ℓ₀))))
       (λ ()
         (@/s 'B (apply and/s (for/list : (Listof Z3-Ast) ([t ts]) (@/s 'is_truish (t))))))]
      [(-@ (-@ 'or/c ps _) es _)
       (define ts : (Listof →Z3-Ast) (for/list ([p ps]) (⦃e⦄! (-@ p es +ℓ₀))))
       (λ ()
         (@/s 'B (apply or/s (for/list : (Listof Z3-Ast) ([t ts]) (@/s 'is_truish (t))))))]
      [(-@ (-@ 'not/c (list p) _) es _)
       (define t (⦃e⦄! (-@ p es +ℓ₀)))
       (λ ()
         (@/s 'B (@/s 'is_false (t))))]
      [(-@ (-struct/c s cs _) es _)
       (define tₚ (⦃e⦄! (-@ (-st-p s) es +ℓ₀)))
       (define ts : (Listof →Z3-Ast)
         (for/list ([(c i) (in-indexed cs)])
           (define eᵢ (-@ (-st-ac s (assert i index?)) es +ℓ₀))
           (⦃e⦄! (-@ c (list eᵢ) +ℓ₀))))
       (λ ()
         (@/s 'B (apply and/s
                        (for/list : (Listof Z3-Ast) ([t (cons tₚ ts)])
                          (@/s 'is_truish (t))))))]
      ;; End of hacks for special applications

      [(-@ (? -o? o) es _)
       (define ts (map ⦃e⦄! es))
       
       (case o ; HACK
         [(list) (refs-add! -cons)]
         [else (refs-add! o)])

       (match o ; HACK
         [(-st-ac 𝒾 _)
          (define n (get-struct-arity 𝒾))
          (define is-St (format-symbol "is-St_~a" n))
          (define tag (format-symbol "tag_~a" n))
          (define stag (-𝒾->-⦃𝒾⦄ 𝒾))
          (match-define (list t) ts)
          (props-add! (λ ()
                        (define tₐ (t))
                        (and/s (@/s is-St tₐ) (=/s (@/s tag tₐ) stag))))]
         [_ (void)])

       (with-handlers ([exn:scv:unsupported?
                        (λ (_)
                          ;; suppress for now
                          (hash-ref!
                           unsupported
                           o
                           (λ ()
                             (log-warning "Z3 translation: unsupported primitive: `~a`~n"
                                          (show-o o))))
                          (define t (fresh-free! 'o))
                          (λ () (val-of t)))])
         (⦃o⦄ o ts))]
      [(-@ eₕ eₓs _)
       (or
        (for/or : (Option →Z3-Ast) ([γ γs])
          (match-define (-γ αₖ blm sₕ sₓs) γ)
          (define xs : (Option (Listof Symbol))
            (match αₖ
              [(-ℬ xs _ _) (and (list? xs) xs)]
              [(-ℳ x _ _ _ _) (list x)]
              [(-ℱ x _ _ _ _) (list x)]))
          (cond [(not xs)
                 (hash-ref! unsupported αₖ
                            (λ () (log-warning "⦃e⦄: ignore ~a for now~n" (show-αₖ αₖ))))
                 #f]
                [(and (equal? eₕ sₕ) (equal? eₓs sₓs))
                 (define fvs
                   (set->list/memo
                    (set-subtract (apply ∪ (fvₛ sₕ) (map fvₛ sₓs))
                                  (list->seteq xs))))
                 (define tₐₚₚ (⦃app⦄! αₖ eₕ fvs eₓs))
                 (app-term! tₐₚₚ)]
                [else #f]))
        (let ([t (fresh-free! 'app)])
          (λ () (val-of t))))]
      [(? -->?)
       (define t (fresh-free! 'arr))
       (props-add! (λ () (@/s 'is-Arr t)))
       (λ () (val-of t))]
      [(? -->i?)
       (define t (fresh-free! 'dep))
       (props-add! (λ () (@/s 'is-ArrD t)))
       (λ () (val-of t))]
      [(? -struct/c?)
       (define t (fresh-free! 'stc))
       (props-add! (λ () (@/s 'is-St/C t)))
       (λ () (val-of t))]
      [(? -•?)
       (define t (fresh-free! 'opq))
       (λ () (val-of t))]
      [_
       (hash-ref!
        unsupported
        e
        (λ ()
          (log-warning "translation: unhandled: ~a~n" (show-e e))))
       (define t (fresh-free! 'unhandled))
       (λ () (val-of t))]))

  (: ⦃γ⦄! : -γ → Void)
  (define (⦃γ⦄! γ)
    (match-define (-γ αₖ blm sₕ sₓs) γ)
    (define xs : (Option (Listof Symbol))
      (match αₖ
        [(-ℬ xs _ _) (and (list? xs) xs)]
        [(-ℳ x _ _ _ _) (list x)]
        [(-ℱ x _ _ _ _) (list x)]
        [(or (? -ℋ𝒱?)) #f]))
    ;; important not to use `-?@` for `eₐₚₚ` as it may simplify away `values` used in `ℳ`
    (define eₐₚₚ (and sₕ (andmap -e? sₓs) (-@ sₕ sₓs +ℓ₀)))
    (unless xs
      (hash-ref! unsupported αₖ (λ () (log-warning "⦃γ⦄: ignore ~a for now~n" (show-αₖ αₖ)))))
    (when (and eₐₚₚ #|TODO|# xs)
      (match-define (-@ eₕ eₓs _) eₐₚₚ)
      (define fvs
        (set->list/memo
         (set-subtract (apply ∪ (fvₛ sₕ) (map fvₛ sₓs))
                       (list->seteq xs))))
      (for ([fv fvs] #:unless (∋ bound fv))
        (free-vars-add! (⦃x⦄ fv)))
      (define tₐₚₚ (⦃app⦄! αₖ eₕ fvs eₓs))
      (match blm
        [(cons l+ lo) (hash-set! asserts-app tₐₚₚ (cons (-l->-⦃l⦄ l+) (-l->-⦃l⦄ lo)))]
        [_            (hash-set! asserts-app tₐₚₚ #t)])))
  
  (for ([γ (reverse γs)]) (⦃γ⦄! γ))
  (for ([φ φs])
    (define t (⦃e⦄! φ))
    (props-add! (λ () (@/s 'is_truish (t)))))
  (define tₜₒₚ (⦃e⦄! e))
  (define all-props
    (∪ (for/seteq: : (℘ →Z3-Ast) ([(tₐₚₚ res) asserts-app])
         (match res
           [#t
            (λ () (@/s 'is-Val (tₐₚₚ)))]
           [(? symbol? t)
            (λ () (=/s (tₐₚₚ) (@/s 'Val (val-of t))))]
           [(cons l+ lo)
            (λ () (=/s (tₐₚₚ) (@/s 'Blm l+ lo)))]))
       props))
  (values refs (Entry free-vars all-props tₜₒₚ)))

(: ⦃o⦄ : -o (Listof →Z3-Ast) → →Z3-Ast)
(define (⦃o⦄ o ts)
  (case o
    [(defined?)
     (λ () (@/s 'B (not/s (=/s 'Undefined ((car ts))))))]
    [(number?)
     (λ () (@/s 'B (@/s 'is-N ((car ts)))))]
    [(real?)
     (λ () (@/s 'B (@/s 'is-R ((car ts)))))]
    [(integer?)
     (λ () (@/s 'B (@/s 'is-Z ((car ts)))))]
    [(symbol?)
     (λ () (@/s 'B (@/s 'is-Sym ((car ts)))))]
    [(string?)
     (λ () (@/s 'B (@/s 'is-Str ((car ts)))))]
    [(procedure?)
     (λ () (@/s 'B (@/s 'is-Proc ((car ts)))))]
    [(boolean?)
     (λ () (@/s 'B (@/s 'is-B ((car ts)))))]
    [(void?)
     (λ () (@/s 'B (=/s 'Void ((car ts)))))]
    [(vector)
     (define i (next-int!))
     (λ () (@/s 'Vec i))]
    [(vector?)
     (λ () (@/s 'B (@/s 'is-Vec ((car ts)))))]
    [(not false?)
     (λ () (@/s 'B (@/s 'is_false ((car ts)))))]
    [(null? empty?)
     (λ () (@/s 'B (=/s 'Null ((car ts)))))]
    [(procedure-arity)
     (λ () (@/s 'N (@/s 'arity ((car ts))) 0))]
    [(arity-includes?)
     (match-define (list a i) ts)
     (λ () (@/s 'B (=/s (a) (i))))]
    [(list)
     (λ ()
       (foldr
        (λ ([tₗ : Z3-Ast] [tᵣ : Z3-Ast])
          (@/s 'St_2 (-𝒾->-⦃𝒾⦄ -𝒾-cons) tₗ tᵣ))
        (val-of 'Null)
        (for/list : (Listof Z3-Ast) ([t ts]) (t))))]
    [(any/c) (λ () (@/s 'B true/s))]
    [(none/c) (λ () (@/s 'B false/s))]
    [(= equal? eq?)
     (match-define (list t₁ t₂) ts)
     (λ () (@/s 'B (=/s (t₁) (t₂))))]
    [(< > <= >=)
     (match-define (list l r) ts)
     (define o/s : (Z3-Ast Z3-Ast → Z3-Ast)
       (case o
         [(<) </s]
         [(<=) <=/s]
         [(>) >/s]
         [else >=/s]))
     (λ ()
       (@/s 'B (o/s (@/s 'real (l)) (@/s 'real (r)))))]
    [(add1)
     (match-define (list t) ts)
     (λ ()
       (@/s 'N (+/s 1 (@/s 'real (t))) (@/s 'imag (t))))]
    [(sub1)
     (match-define (list t) ts)
     (λ ()
       (@/s 'N (-/s (@/s 'real (t)) 1) (@/s 'imag (t))))]
    [(+ -)
     (match-define (list x y) ts)
     (define o/s : (Smt-Expr Smt-Expr → Z3-Ast)
       (case o
         [(+) +/s]
         [else -/s]))
     (λ ()
       (@/s 'N
            (o/s (@/s 'real (x)) (@/s 'real (y)))
            (o/s (@/s 'imag (x)) (@/s 'imag (y)))))]
    [(*)
     (match-define (list x y) ts)
     (λ ()
       (define xₐ (x))
       (define yₐ (y))
       (define a (@/s 'real xₐ))
       (define b (@/s 'imag xₐ))
       (define c (@/s 'real yₐ))
       (define d (@/s 'imag yₐ))
       (@/s 'N
            (-/s (*/s a c) (*/s b d))
            (+/s (*/s a d) (*/s b c))))]
    [(/)
     (match-define (list x y) ts)
     (λ ()
       (define xₐ (x))
       (define yₐ (y))
       (define a (@/s 'real xₐ))
       (define b (@/s 'imag xₐ))
       (define c (@/s 'real yₐ))
       (define d (@/s 'imag yₐ))
       (define c²d² (+/s (*/s c c) (*/s d d)))
       (@/s 'N
            (//s (+/s (*/s a c) (*/s b d)) c²d²)
            (//s (-/s (*/s b c) (*/s a d)) c²d²)))]
    [(sqrt) ; just for real numbers for now
     (match-define (list t) ts)
     (λ ()
       (@/s 'N (^/s (@/s 'real (t)) 0.5) 0))]
    [(zero?)
     (match-define (list t) ts)
     (λ ()
       (@/s 'B (=/s (@/s 'N 0 0) (t))))]
    [(positive?)
     (match-define (list t) ts)
     (λ ()
       (define tₐ (t))
       (@/s 'B
            (and/s (@/s 'is-R tₐ)
                   (>/s (@/s 'real tₐ) 0))))]
    [(negative?)
     (match-define (list t) ts)
     (λ ()
       (define tₐ (t))
       (@/s 'B
            (and/s (@/s 'is-R tₐ)
                   (</s (@/s 'real tₐ) 0))))]
    [(exact-nonnegative-integer?)
     (match-define (list t) ts)
     (λ ()
       (define tₐ (t))
       (@/s 'B (and/s (@/s 'is-Z tₐ)
                      (@/s 'exact? tₐ)
                      (>=/s (@/s 'real tₐ) 0))))]
    [(exact-positive-integer?)
     (match-define (list t) ts)
     (λ ()
       (define tₐ (t))
       (@/s 'B (and/s (@/s 'is-Z tₐ)
                      (@/s 'exact? tₐ)
                      (>/s (@/s 'real tₐ) 0))))]
    ;; HERE
    [(inexact?)
     (λ ()
       (@/s 'B (@/s 'inexact? ((car ts)))))]
    [(exact?)
     (λ ()
       (@/s 'B (@/s 'exact? ((car ts)))))]
    [(string-length)
     (λ ()
       (@/s 'N (@/s 'strlen ((car ts))) 0))]
    [(and/c)
     (define i (next-int!))
     (λ () (@/s 'And/C i))]
    [(or/c)
     (define i (next-int!))
     (λ () (@/s 'Or/C i))]
    [(not/c)
     (define i (next-int!))
     (λ () (@/s 'Not/C i))]
    [(vector-ref)
     (match-define (list t₁ t₂) ts)
     (λ () (@/s 'f.vecref (t₁) (t₂)))]
    [(vector-length)
     (λ () (@/s 'N (@/s 'veclen ((car ts))) 0))]
    [(list?)
     (λ () (@/s 'B (@/s 'list? ((car ts)))))]
    [(map)
     (match-define (list t₁ t₂) ts)
     (λ () (@/s 'f.map (t₁) (t₂)))]
    [(append)
     (match-define (list t₁ t₂) ts)
     (λ () (@/s 'f.append (t₁) (t₂)))]
    [(min)
     (match-define (list t₁ t₂) ts)
     (λ () (@/s 'N (@/s 'f.min (@/s 'real (t₁)) (@/s 'real (t₂))) 0))]
    [(max)
     (match-define (list t₁ t₂) ts)
     (λ () (@/s 'N (@/s 'f.max (@/s 'real (t₁)) (@/s 'real (t₂))) 0))]
    [else
     (match o
       [(-st-p 𝒾)
        (define n (get-struct-arity 𝒾))
        (define is-St (format-symbol "is-St_~a" n))
        (define st-tag (format-symbol "tag_~a" n))
        (define tag (-𝒾->-⦃𝒾⦄ 𝒾))
        (match-define (list t) ts)
        (λ ()
          (define tₐ (t))
          (@/s 'B (and/s (@/s is-St tₐ)
                         (=/s (@/s st-tag tₐ) tag))))]
       [(-st-mk 𝒾)
        (define St (format-symbol "St_~a" (get-struct-arity 𝒾)))
        (λ ()
          (apply @/s St (-𝒾->-⦃𝒾⦄ 𝒾) (run-all ts)))]
       [(-st-ac 𝒾 i)
        (define field (format-symbol "field_~a_~a" (get-struct-arity 𝒾) i))
        (λ () (@/s field ((car ts))))]
       [_ (raise (exn:scv:unsupported (format "unsupported: ~a" (show-o o))
                                          (current-continuation-marks)))])]))

(: ⦃p⦄ : (U -o -λ) →Z3-Ast → →Z3-Ast)
(define (⦃p⦄ p t)
  (match p
    [(? -o? o) (⦃o⦄ o (list t))]
    [(-λ (list x) (-@ (? -o? o) (list (-x x) (-b b)) _))
     (⦃o⦄ o (list t (λ () (⦃b⦄ b))))]
    [(-λ (list x) (-@ (? -o? o) (list (-b b) (-x x)) _))
     (⦃o⦄ o (list (λ () (⦃b⦄ b)) t))]))

(: ⦃b⦄ : Base → Z3-Ast)
(define (⦃b⦄ b)
  (match b
    [#f (@/s 'B false/s)]
    [#t (@/s 'B true/s)]
    [(? number? x) (@/s 'N (real-part x) (imag-part x))]
    [(? symbol? s) (@/s 'Sym (Symbol->⦃Symbol⦄ s))]
    [(? string? s) (@/s 'Str (String->⦃String⦄ s))]
    [(? void?) (val-of 'Void)]
    [(? char? c) (@/s 'Chr (Char->⦃Char⦄ c))]
    [(list) (val-of 'Null)]
    [_ (error '⦃b⦄ "value: ~a" b)]))

(: base-datatypes : (℘ Natural) → Void)
(define (base-datatypes arities)
  (define st-defs : (Listof (Pairof Symbol (Listof (List Symbol Smt-Sort-Expr))))
    (for/list ([n (set-add arities #|hack|# 2)])
      (define St_k (format-symbol "St_~a" n))
      (define tag_k (format-symbol "tag_~a" n))
      (define fields
        (for/list : (Listof (List Symbol Smt-Sort-Expr)) ([i n])
          `(,(format-symbol "field_~a_~a" n i) V)))
      `(,St_k (,tag_k ,Int/s) ,@fields)))
  (dynamic-declare-datatype
   'V
   `(Undefined
     Null
     Void
     (N [real ,Real/s] [imag ,Real/s])
     (B [unbox_B ,Bool/s])
     (Proc [proc_id ,Int/s])
     (Sym [sym ,Int/s])
     (Str [str ,Int/s])
     (Chr [chr ,Int/s])
     (And/C [and/c_id ,Int/s])
     (Or/C [or/c_id ,Int/s])
     (Not/C [not/c_id ,Int/s])
     (St/C [st/c_id ,Int/s])
     (Arr [arr_id ,Int/s])
     (ArrD [arrD_id ,Int/s])
     (Vec [unbox_Vec ,Int/s])
     ,@st-defs))
  (declare-datatype
   A
   (Val [unbox_Val 'V])
   (Blm [blm_pos Int/s] [blm_src Int/s])
   None)
  (void))

(: base-predicates : (℘ -o) → Void)
(define (base-predicates prims)
  ;; Primitive predicates
  (define-fun is_false ([x 'V]) Bool/s
    (=/s x (@/s 'B false/s)))
  (define-fun is_truish ([x 'V]) Bool/s
    (not/s (@/s 'is_false x)))
  (define-fun is-R ([x 'V]) Bool/s
    (and/s (@/s 'is-N x) (=/s 0 (@/s 'imag x))))
  (define-fun is-Z ([x 'V]) Bool/s
    (and/s (@/s 'is-R x) (is-int/s (@/s 'real x))))

  (unless (set-empty? (∩ prims (set 'exact? 'exact-integer? 'exact-nonnegative-integer? 'exact-positive-integer?)))
    (dynamic-declare-fun 'exact? '(V) Bool/s))
  
  (when (∋ prims 'inexact?)
    (dynamic-declare-fun 'inexact? '(V) Bool/s))
  
  (when (∋ prims 'string-length)
    (dynamic-declare-fun 'strlen '(V) Int/s)
    (assert! (∀/s ([v 'V]) (>=/s (@/s 'strlen v) 0))))

  (when (∋ prims 'vector-ref)
    (dynamic-declare-fun 'f.vecref '(V V) 'V))
  
  (when (∋ prims 'vector-length)
    (dynamic-declare-fun 'veclen '(V) Int/s)
    (assert! (∀/s ([v 'V]) (>=/s (@/s 'veclen v) 0))))

  (when #t #;(∋ prims 'procedure-arity)
    (dynamic-declare-fun 'arity '(V) Int/s)
    (assert! (∀/s ([v 'V]) (>=/s (@/s 'arity v) 0))))
  
  (when (∋ prims 'list?)
    (dynamic-declare-fun 'list? '(V) Bool/s)
    (assert! (@/s 'list? 'Null))
    (assert! (∀/s ([h 'V] [t 'V])
                  (=>/s (@/s 'list? t) (@/s 'list? (@/s 'St_2 (-𝒾->-⦃𝒾⦄ -𝒾-cons) h t))))))

  (when (∋ prims 'map)
    (dynamic-declare-fun 'f.map '(V V) 'V))
  
  (when (∋ prims 'append)
    (dynamic-declare-fun 'f.append '(V V) 'V))

  (when (∋ prims 'min)
    (dynamic-define-fun 'f.min ([x Real/s] [y Real/s]) Real/s (ite/s (<=/s x y) x y)))
  
  (when (∋ prims 'max)
    (dynamic-define-fun 'f.max ([x Real/s] [y Real/s]) Real/s (ite/s (>=/s x y) x y)))
  
  (void))

(define-interner -o #:interned-type-name -⦃o⦄)
(define-interner Symbol #:interned-type-name ⦃Symbol⦄)
(define-interner String #:interned-type-name ⦃String⦄)
(define-interner Char #:interned-type-name ⦃Char⦄)
(define-interner -l #:interned-type-name -⦃l⦄)
(define-interner -𝒾 #:interned-type-name -⦃𝒾⦄)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Emitting SMT 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: emit : (℘ -o) Memo-Table Entry → (Values →Void →Z3-Ast))
(define (emit prims def-funs top)
  (match-define (Entry consts facts goal) top)

  (define st-arities
    (for/fold ([acc : (℘ Index) ∅eq])
              ([o (in-set prims)])
      (match o
        [(or (-st-mk 𝒾) (-st-p 𝒾) (-st-ac 𝒾 _) (-st-mut 𝒾 _)) #:when 𝒾
         (set-add acc (get-struct-arity 𝒾))]
        [(or 'list? 'list-ref 'map)
         (set-add acc 2)]
        [_ acc])))
  
  (define-values (emit-dec-funs emit-def-funs)
    (for/fold ([decs : (Listof →Void) '()]
               [defs : (Listof →Void) '()])
              ([(f-xs res) def-funs])
      (match-define (App αₖ fvs) f-xs)
      (define xs : (Listof Symbol)
        (match αₖ
          [(-ℬ xs _ _)
           (cond [(list? xs) xs]
                 [else
                  (hash-ref! unsupported αₖ (λ () (log-warning "unsupported: ~a~n" (show-αₖ αₖ))))
                  '()])]
          [(-ℳ x _ _ _ _) (list x)]
          [(-ℱ x _ _ _ _) (list x)]))
      (define n (+ (length fvs) (length xs)))
      (define ⦃fv⦄s (map ⦃x⦄ fvs))
      (define tₓs : (Listof →Z3-Ast)
        (for/list ([x xs])
          (define t (⦃x⦄ x))
          (λ () (val-of t))))
      (define fₕ (fun-name f-xs))
      (define tₐₚₚ (-tapp fₕ ⦃fv⦄s tₓs))
      (match-define (Res oks ers) res)

      (: mk-cond : (Listof Entry) → →Z3-Ast)
      (define (mk-cond entries)
        (match entries
          ['() (λ () false/s)]
          [(list ent)
           (match-define (Entry xs facts _) ent)
           (λ ()
             (∃/V xs (apply and/s (run-all (set->list facts)))))]
          [_
           (define-values (shared-xs shared-cond)
             (for/fold ([shared-xs : (℘ Symbol) (Entry-free-vars (first entries))]
                        [shared-cond : (℘ →Z3-Ast) (Entry-facts (first entries))])
                       ([ent (in-list (rest entries))])
               (match-define (Entry xs φs _) ent)
               (values (∩ shared-xs xs) (∩ shared-cond φs))))
           (define disjs
             (for/list : (Listof →Z3-Ast) ([ent entries])
               (match-define (Entry xs₀ φs₀ _) ent)
               (define xs (set-subtract xs₀ shared-xs))
               (define φs (set-subtract φs₀ shared-cond))
               (λ () (∃/V xs (apply and/s (run-all (set->list φs)))))))
           (λ ()
             (∃/V shared-xs (apply and/s
                                   (append (run-all (set->list shared-cond))
                                           (list (apply or/s (run-all disjs)))))))]))

      (define ok-cond (mk-cond oks))
      (define er-cond (mk-cond ers))
      (define params : (Listof Symbol) (append ⦃fv⦄s (map ⦃x⦄ xs)))
      
      (values
       (cons
        (λ ()
          (void (dynamic-declare-fun fₕ (make-list n 'V) 'A)))
        decs)
       (cons
        (λ ()
          (assert! (∀/V params (=>/s (@/s 'is-Val (tₐₚₚ)) (ok-cond))
                           #:pattern (list (pattern-of (tₐₚₚ)))))
          (assert! (∀/V params (=>/s (@/s 'is-Blm (tₐₚₚ)) (er-cond))
                           #:pattern (list (pattern-of (tₐₚₚ))))))
        defs))))

  (define (emit-dec-consts)
    (for ([x consts])
      (dynamic-declare-const x 'V)))

  (define (emit-asserts)
    (for ([φ facts])
      (assert! (φ))))

  (values (λ ()
            (base-datatypes st-arities)
            (base-predicates prims)
            (emit-dec-consts)
            (run-all emit-dec-funs)
            (run-all emit-def-funs)
            (emit-asserts))
          goal))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (quant/V quant xs* e #:pattern pats)
  (let ([xs xs*])
    (define ts : (Listof Symbol) (for/list ([x xs]) 'V))
    (quant xs ts e #:pattern pats)))
(define-simple-macro (∃/V xs e (~optional (~seq #:pattern pats) #:defaults ([(pats 0) #'null])))
  (quant/V dynamic-∃/s xs e #:pattern pats))
(define-simple-macro (∀/V xs e (~optional (~seq #:pattern pats) #:defaults ([(pats 0) #'null])))
  (quant/V dynamic-∀/s xs e #:pattern pats))

(: run-all (∀ (X) (Listof (→ X)) → (Listof X)))
(define (run-all fs) (for/list ([f fs]) (f)))

(: -tapp : Symbol (Listof Symbol) (Listof →Z3-Ast) → →Z3-Ast)
(define (-tapp f fvs args)
  (cond
    [(and (null? fvs) (null? args))
     (λ () (val-of f))]
    [else
     (λ ()
       (define all-args
         (append
          (for/list : (Listof Z3-Ast) ([fv fvs])
            (val-of fv))
          (for/list : (Listof Z3-Ast) ([arg args])
            (arg))))
       (apply @/s f all-args))]))

(: fun-name : App → Symbol)
(define fun-name
  (let ([m : (HashTable App Symbol) (make-hash)])
    (λ (app)
      (hash-ref! m app (λ () (format-symbol "f.~a" (hash-count m)))))))

(: ⦃𝒾⦄ : -𝒾 → Symbol)
(define (⦃𝒾⦄ 𝒾)
  (format-symbol "t.~a" (string->symbol (fix-name (symbol->string (-𝒾-name 𝒾))))))

(: ⦃x⦄ : Symbol → Symbol)
(define (⦃x⦄ x)
  (cond [(integer? x) (format-symbol "x.~a" x)]
        [else (string->symbol (fix-name (symbol->string x)))]))

(: fix-name : String → String)
(define (fix-name s)

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
      [(#\:) '(#\_)]
      [else (list c)]))

  (list->string (append-map subst (string->list s))))

(: next-int! : → Natural)
(define next-int!
  (let ([i : Natural 0])
    (λ ()
      (begin0 i (set! i (+ 1 i))))))

;; memoize to ensure fixed order
(define/memo (set->list/memo [xs : (Setof Symbol)]) : (Listof Symbol) (set->list xs))
