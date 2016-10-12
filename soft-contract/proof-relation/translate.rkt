#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base)
         racket/match
         racket/set
         racket/string
         syntax/parse/define
         z3/smt
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt")

(struct exn:scv:unsupported exn () #:transparent)
(define-type →Z3-Ast (→ Z3-Ast))
(define-type →Void   (→ Void))

(define unsupported : (HashTable Any Void) (make-hash))

(struct Entry ([free-vars : (℘ Symbol)]
               [facts     : (℘ →Z3-Ast)]
               [expr      : →Z3-Ast])
  #:transparent)
(struct App ([ctx : -αₖ] [fvs : (Listof Var-Name)] [params : (Listof Var-Name)]) #:transparent)
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

;(: encode : -M -Γ -e → (Values →Void →Z3-Ast))
;; Encode `M Γ ⊢ e` into a pair of thunks that emit assertions and goal to check for
;; satisfiability
(define/memo (encode [M : -M] [Γ : -Γ] [e : -e]) : (Pairof →Void →Z3-Ast)
  (match-define (cons refs top-entry) (encode-e ∅ ∅eq Γ e))
  (let loop ([fronts   : (℘ Defn-Entry) refs]
             [seen     : (℘ Defn-Entry) refs]
             [def-funs : Memo-Table (hash)])
    (cond
      [(set-empty? fronts)
       (define st-arities
         (for/fold ([acc : (℘ Natural) ∅eq])
                   ([entry seen])
           (match entry
             [(or (-st-mk s) (-st-p s) (-st-ac s _) (-st-mut s _)) #:when s
              (set-add acc (-struct-info-arity s))]
             [(or 'list? 'list-ref 'map)
              (set-add acc 2)]
             [_ acc])))
       (emit st-arities def-funs top-entry)]
      [else
       (define-values (fronts* seen* def-funs*)
         (for/fold ([fronts*   : (℘ Defn-Entry) ∅]
                    [seen*     : (℘ Defn-Entry) seen]
                    [def-funs* : Memo-Table def-funs])
                   ([front fronts])
           (define-values (def-funs** refs+)
             (match front
               [(and app-ctx (App-Ctx (and app (App αₖ _ _)) _))
                (define As (M@ M αₖ))
                (match-define (cons refs entries) (encode-App-Ctx app-ctx As))
                (values (hash-set def-funs* app entries) refs)]
               [(? -o? o)
                (values def-funs* ∅)]))
           (define-values (fronts** seen**)
             (for/fold ([fronts** : (℘ Defn-Entry) fronts*]
                        [seen**   : (℘ Defn-Entry) seen*])
                       ([ref refs+] #:unless (∋ seen** ref))
               (values (set-add fronts** ref)
                       (set-add seen**   ref))))
           (values fronts** seen** def-funs**)))
       (loop fronts* seen* def-funs*)])))

;; Translate memo-table entry `αₖ(xs) → {A…}` to pair of formulas for when application
;; fails and passes
(define/memo (encode-App-Ctx [app-ctx : App-Ctx] [ΓAs : (℘ -ΓA)]) : (Pairof (℘ Defn-Entry) Res)
  (define-set refs : Defn-Entry)
  (match-define (App-Ctx app ctx) app-ctx)
  (match-define (App αₖ fvs xs) app)
  (define ⦃fv⦄s (map ⦃x⦄ fvs))
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
        [(-W _ sₐ)
         (define eₒₖ
           (cond
             [sₐ
              (match-define (cons refs+ entry) (encode-e ctx bound Γ sₐ))
              (refs-union! refs+)
              (match-define (Entry free-vars facts tₐₙₛ) entry)
              (Entry free-vars
                     (set-add facts (λ () (=/s (tₐₚₚ) (@/s 'Val (tₐₙₛ)))))
                     tₐₙₛ)]
             [else
              (match-define (cons refs+ entry) (encode-e ctx bound Γ #|HACK|# -ff))
              (refs-union! refs+)
              (match-define (Entry free-vars facts _) entry)
              (Entry free-vars facts #|hack|# (λ () (@/s 'B false/s)))]))
         (values (cons eₒₖ oks) ers)]
        [(-blm l+ lo _ _)
         (define eₑᵣ
           (match-let ([(cons refs+ entry) (encode-e ctx bound Γ #|hack|# -ff)])
             (refs-union! refs+)
             (match-define (Entry free-vars facts _) entry)
             (Entry free-vars
                    (set-add facts (λ () (=/s (tₐₚₚ) (@/s 'Blm (⦃l⦄ l+) (⦃l⦄ lo)))))
                    #|HACK|# (λ () (@/s 'B false/s)))))
         (values oks (cons eₑᵣ ers))])))
  (cons refs (Res oks ers)))

;(: encode-e : (℘ Var-Name) -Γ -e → (Values (℘ Defn-Entry) Entry))
;; Encode path-condition `Γ` and expression `e` into a
;; - a Z3-Ast-producing thunk, and
;; - a set of function definitions to encode
(define/memo (encode-e [trace : App-Trace]
                       [bound : (℘ Var-Name)]
                       [Γ : -Γ]
                       [e : -e]) : (Pairof (℘ Defn-Entry) Entry)
  
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

  ;; Add a reminder to encode memo table entries for `αₖ(xs)` as a 1st-order function
  (define/memo (⦃fun⦄! [eₕ : -e] [app : App]) : Symbol
     (⦃e⦄! eₕ) ; for "side-effect" of `eₕ` having evaluated
     (refs-add! (App-Ctx app (set-add trace app)))
     (fun-name app))

  ;; encode application
  (define/memo (⦃app⦄!
                [αₖ : -αₖ]
                [eₕ : -e]
                [fvs : (Listof Var-Name)]
                [xs : (Listof Var-Name)]
                [eₓs : (Listof -e)]) : →Z3-Ast
    (define app (App αₖ fvs xs))
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
       (define id (o->id o))
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
      [(-@ (-@ (or 'and/c (-𝒾 'and/c 'Λ)) ps _) es _)
       (define ts : (Listof →Z3-Ast) (for/list ([p ps]) (⦃e⦄! (-@ p es +ℓ₀))))
       (λ ()
         (@/s 'B (apply and/s (for/list : (Listof Z3-Ast) ([t ts]) (@/s 'is_truish (t))))))]
      [(-@ (-@ (or 'or/c (-𝒾 'or/c 'Λ)) ps _) es _)
       (define ts : (Listof →Z3-Ast) (for/list ([p ps]) (⦃e⦄! (-@ p es +ℓ₀))))
       (λ ()
         (@/s 'B (apply or/s (for/list : (Listof Z3-Ast) ([t ts]) (@/s 'is_truish (t))))))]
      [(-@ (-@ (or 'not/c (-𝒾 'not/c 'Λ)) (list p) _) es _)
       (define t (⦃e⦄! (-@ p es +ℓ₀)))
       (λ ()
         (@/s 'B (@/s 'is_false (t))))]
      [(-@ (-struct/c s cs _) es _)
       (define tₚ (⦃e⦄! (-@ (-st-p s) es +ℓ₀)))
       (define ts : (Listof →Z3-Ast)
         (for/list ([(c i) (in-indexed cs)])
           (define eᵢ (-@ (-st-ac s (assert i exact-nonnegative-integer?)) es +ℓ₀))
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
         [(-st-ac s _)
          (define n (-struct-info-arity s))
          (define is-St (format-symbol "is-St_~a" n))
          (define tag (format-symbol "tag_~a" n))
          (define stag (⦃struct-info⦄ s))
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
                             (printf "Z3 translation: unsupported primitive: `~a`~n"
                                     (show-o o))))
                          (define t (fresh-free! 'o))
                          (λ () (val-of t)))])
         (app-o o ts))]
      [(-@ eₕ eₓs _)
       (or
        (for/or : (Option →Z3-Ast) ([γ γs])
          (match-define (-γ αₖ (cons sₕ sₓs) blm) γ)
          (define xs : (Option (Listof Var-Name))
            (match αₖ
              [(-ℬ xs _ _) (and (list? xs) xs)]
              [(-ℳ x _ _ _ _) (list x)]
              [(-ℱ x _ _ _ _) (list x)]))
          (cond [(not xs)
                 (hash-ref! unsupported αₖ
                            (λ () (printf "⦃e⦄: ignore ~a for now~n" (show-αₖ αₖ))))
                 #f]
                [(equal? eₕ sₕ)
                 (define fvs
                   (set->list/memo
                    (set-subtract (apply ∪ (fvₛ sₕ) (map fvₛ sₓs))
                                  (list->seteq xs))))
                 (define tₐₚₚ (⦃app⦄! αₖ eₕ fvs xs eₓs))
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
          (printf "translation: unhandled: ~a~n" (show-e e))))
       (define t (fresh-free! 'unhandled))
       (λ () (val-of t))]))

  (: ⦃γ⦄! : -γ → Void)
  (define (⦃γ⦄! γ)
    (match-define (-γ αₖ (cons sₕ sₓs) blm) γ)
    (define xs : (Option (Listof Var-Name))
      (match αₖ
        [(-ℬ xs _ _) (and (list? xs) xs)]
        [(-ℳ x _ _ _ _) (list x)]
        [(-ℱ x _ _ _ _) (list x)]))
    (define eₐₚₚ (apply -?@ sₕ sₓs))
    (unless xs
      (hash-ref! unsupported αₖ (λ () (printf "⦃γ⦄: ignore ~a for now~n" (show-αₖ αₖ)))))
    (when (and eₐₚₚ #|TODO|# xs)
      (match-define (-@ eₕ eₓs _) eₐₚₚ)
      (define fvs
        (set->list/memo
         (set-subtract (apply ∪ (fvₛ sₕ) (map fvₛ sₓs))
                       (list->seteq xs))))
      (for ([fv fvs] #:unless (∋ bound fv))
        (free-vars-add! (⦃x⦄ fv)))
      (define tₐₚₚ (⦃app⦄! αₖ eₕ fvs xs eₓs))
      (match blm
        [(cons l+ lo) (hash-set! asserts-app tₐₚₚ (cons (⦃l⦄ l+) (⦃l⦄ lo)))]
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
  (cons refs (Entry free-vars all-props tₜₒₚ))
  )

;(: app-o : -o (Listof →Z3-Ast) → →Z3-Ast)
(define/memo (app-o [o : -o] [ts : (Listof →Z3-Ast)]) : →Z3-Ast
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
          (@/s 'St_2 (⦃struct-info⦄ -s-cons) tₗ tᵣ))
        (val-of 'Null)
        (for/list : (Listof Z3-Ast) ([t ts]) (t))))]
    [(any/c) (λ () (@/s 'B true/s))]
    [(none/c) (λ () (@/s 'B false/s))]
    [(= equal?)
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
    [(exact-nonnegative-integer?)
     (match-define (list t) ts)
     (λ ()
       (define tₐ (t))
       (@/s 'B (and/s (@/s 'is-Z tₐ)
                      (@/s 'exact? tₐ)
                      (>=/s (@/s 'real tₐ) 0))))]
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
       [(-st-p s)
        (define n (-struct-info-arity s))
        (define is-St (format-symbol "is-St_~a" n))
        (define st-tag (format-symbol "tag_~a" n))
        (define tag (⦃struct-info⦄ s))
        (match-define (list t) ts)
        (λ ()
          (define tₐ (t))
          (@/s 'B (and/s (@/s is-St tₐ)
                         (=/s (@/s st-tag tₐ) tag))))]
       [(-st-mk s)
        (define St (format-symbol "St_~a" (-struct-info-arity s)))
        (λ ()
          (apply @/s St (⦃struct-info⦄ s) (run-all ts)))]
       [(-st-ac s i)
        (define field (format-symbol "field_~a_~a" (-struct-info-arity s) i))
        (λ () (@/s field ((car ts))))]
       [_ (raise (exn:scv:unsupported (format "unsupported: ~a" (show-o o))
                                          (current-continuation-marks)))])]))

(: ⦃b⦄ : Base → Z3-Ast)
(define (⦃b⦄ b)
  (match b
    [#f (@/s 'B false/s)]
    [#t (@/s 'B true/s)]
    [(? number? x) (@/s 'N (real-part x) (imag-part x))]
    [(? symbol? s) (@/s 'Sym (⦃sym⦄ s))]
    [(? string? s) (@/s 'Str (⦃str⦄ s))]
    [(? void?) (val-of 'Void)]
    [(list) (val-of 'Null)]
    [_ (error '⦃b⦄ "value: ~a" b)]))

(: SMT-base : (℘ Natural) → Void)
(define (SMT-base struct-arities)
  (base-datatypes struct-arities)
  (base-predicates))

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

(: base-predicates : →Void)
(define (base-predicates)
  ;; Primitive predicates
  (define-fun is_false ([x V]) Bool/s
    (=/s x (@/s 'B false/s)))
  (define-fun is_truish ([x V]) Bool/s
    (not/s (@/s 'is_false x)))
  (define-fun is-R ([x V]) Bool/s
    (and/s (@/s 'is-N x) (=/s 0 (@/s 'imag x))))
  (define-fun is-Z ([x V]) Bool/s
    (and/s (@/s 'is-R x) (is-int/s (@/s 'real x))))
  (declare-fun exact? ('V) Bool/s)
  (declare-fun inexact? ('V) Bool/s)
  (declare-fun strlen ('V) Int/s)
  (declare-fun f.vecref ('V 'V) 'V)
  (declare-fun veclen ('V) Int/s)
  (assert! (∀/s ([v 'V]) (>=/s (strlen v) 0)))
  (assert! (∀/s ([v 'V]) (>=/s (veclen v) 0)))
  (declare-fun arity ('V) Int/s)
  (assert! (∀/s ([v 'V]) (>=/s (arity v) 0)))
  (declare-fun list? ('V) Bool/s)
  (assert! (list? 'Null))
  (assert! (∀/s ([h 'V] [t 'V])
                (=>/s (list? t) (list? (@/s 'St_2 (⦃struct-info⦄ -s-cons) h t)))))
  (declare-fun f.map ('V 'V) 'V)
  (declare-fun f.append ('V 'V) 'V)
  (define-fun f.min ([x Real/s] [y Real/s]) Real/s (ite/s (<=/s x y) x y))
  (define-fun f.max ([x Real/s] [y Real/s]) Real/s (ite/s (>=/s x y) x y))
  (void))

(define o->id ((inst mk-interner -o)))
(define ⦃sym⦄ ((inst mk-interner Symbol) #:eq? #t))
(define ⦃str⦄ ((inst mk-interner String)))
(define ⦃l⦄ ((inst mk-interner -l)))
(define ⦃struct-info⦄ ((inst mk-interner -struct-info)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Emitting SMT 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(: emit : (℘ Natural) Memo-Table Entry → (Values →Void →Z3-Ast))
(define/memo (emit [struct-arities : (℘ Natural)]
                   [def-funs : Memo-Table]
                   [top : Entry]) : (Pairof →Void →Z3-Ast)
  (match-define (Entry consts facts goal) top)
  
  (define-values (emit-dec-funs emit-def-funs)
    (for/fold ([decs : (Listof →Void) '()]
               [defs : (Listof →Void) '()])
              ([(f-xs res) def-funs])
      (match-define (App αₖ fvs xs) f-xs)
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

  (cons (λ ()
            (SMT-base struct-arities)
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

;(: -tapp : Symbol (Listof Symbol) (Listof →Z3-Ast) → →Z3-Ast)
(define/memo (-tapp [f : Symbol] [fvs : (Listof Symbol)] [args : (Listof →Z3-Ast)]) : →Z3-Ast
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

(: ⦃x⦄ : Var-Name → Symbol)
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
(define/memo (set->list/memo [xs : (Setof Var-Name)]) : (Listof Var-Name) (set->list xs))
