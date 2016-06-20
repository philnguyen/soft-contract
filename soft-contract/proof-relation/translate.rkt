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

(: SMT-base : (℘ Natural) → (Listof Sexp))
(define (SMT-base struct-arities)
  `(,@(base-datatypes struct-arities)
    ,@base-predicates))

;; SMT target language
(define-type Term Sexp)
(define-type Formula Sexp) ; Term of type Bool in SMT
(struct Entry ([free-vars : (℘ Symbol)] [facts : (℘ Formula)] [expr : Term]) #:transparent)
(struct App ([ctx : -τ] [fvs : (Listof Var-Name)] [params : (Listof Var-Name)]) #:transparent)
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
         (for/fold ([fronts* : (℘ Defn-Entry) ∅]
                    [seen* : (℘ Defn-Entry) seen]
                    [def-funs* : Memo-Table def-funs])
                   ([front fronts])
           (define-values (def-funs** refs+)
             (match front
               [(App τ fvs xs)
                (define As (hash-ref M τ))
                (define-values (refs entries) (encode-τ τ fvs xs As))
                (values (hash-set def-funs* front entries) refs)]
               [(? -o? o)
                (values def-funs* ∅)]))
           
           (define-values (fronts** seen**)
             (for/fold ([fronts** : (℘ Defn-Entry) fronts*]
                        [seen** : (℘ Defn-Entry) seen*])
                       ([ref refs+] #:unless (∋ seen** ref))
               (values (set-add fronts** ref)
                       (set-add seen** ref))))
           (values fronts** seen** def-funs**)))
       (loop fronts* seen* def-funs*)])))

(: encode-τ : -τ (Listof Var-Name) (Listof Var-Name) (℘ -A) → (Values (℘ Defn-Entry) Res))
;; Translate memo-table entry `τ(xs) → {A…}` to pair of formulas for when application
;; fails and passes
(define (encode-τ τ fvs xs As)
  (define-set refs : Defn-Entry)
  (define ⦃fv⦄s (map ⦃x⦄ fvs))
  (define tₓs (map ⦃x⦄ xs))
  (define fₕ (fun-name τ fvs xs))
  (define tₐₚₚ (-tapp fₕ ⦃fv⦄s tₓs))
  (define bound (∪ (list->seteq fvs) (list->seteq xs)))
  
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
                     (set-add facts `(= ,tₐₚₚ (Val ,tₐₙₛ)))
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
                    (set-add facts `(= ,tₐₚₚ (Blm ,(⦃l⦄ l+) ,(⦃l⦄ lo))))
                    #|hack|# `(B false))))
         (values oks (cons eₑᵣ ers))])))
  
  (values refs (Res oks ers)))

(: encode-e : (℘ Var-Name) -Γ -e → (Values (℘ Defn-Entry) Entry))
;; Encode pathcondition `Γ` and expression `e`,
(define (encode-e bound Γ e)

  (define-set free-vars : Symbol #:eq? #t)
  (define-set props : Formula)
  (define asserts-app : (HashTable Term (U #t ; is-Val
                                           Symbol ; is-Val + instantiate
                                           (Pairof Integer Integer) ; blm
                                           ))
    (make-hash))
  (define-set refs : Defn-Entry)
  (match-define (-Γ φs _ γs) Γ)

  (define fresh-free! : (→ Symbol)
    (let ([i : Natural 0])
      (λ ()
        (define x (format-symbol "i.~a" i))
        (set! i (+ 1 i))
        (free-vars-add! x)
        x)))

  (define app-term! : (Term → Symbol)
    (let ([m : (HashTable Term Symbol) (make-hash)])
      (λ (tₐₚₚ)
        (hash-ref! m tₐₚₚ (λ ()
                            (define tₐ (format-symbol "a.~a" (hash-count m)))
                            (free-vars-add! tₐ)
                            (hash-set! asserts-app tₐₚₚ tₐ)
                            tₐ)))))

  ;; Add a reminder to encode memo table entries for `τ(xs)` as a 1st-order function
  (define/memo (⦃fun⦄! [τ : -τ] [eₕ : -e] [fvs : (Listof Var-Name)] [xs : (Listof Var-Name)]) : Symbol
    (define _ (⦃e⦄! eₕ))
    (define ⦃fv⦄s (map ⦃x⦄ fvs))
    (refs-add! (App τ fvs xs))
    (fun-name τ fvs xs))

  ;; Encode application
  (define/memo (⦃app⦄! [τ : -τ] [eₕ : -e] [fvs : (Listof Var-Name)] [xs : (Listof Var-Name)] [eₓs : (Listof -e)]) : Term
    (define fₕ (⦃fun⦄! τ eₕ fvs xs))
    (-tapp fₕ (map ⦃x⦄ fvs) (map ⦃e⦄! eₓs)))

  ;; encode the fact that `e` has successfully evaluated
  (define/memo (⦃e⦄! [e : -e]) : Term
    ;(printf "⦃e⦄!: ~a~n" (show-e e))
    (match e
      [(-b b) (⦃b⦄ b)]
      [(? -𝒾? 𝒾)
       (define t (⦃𝒾⦄ 𝒾))
       (free-vars-add! t)
       t]
      [(? -o? o) `(Proc ,(o->id o))]
      [(-x x)
       (define t (⦃x⦄ x))
       (cond [(∋ bound x) t]
             [else (free-vars-add! t) t])]
      [(-λ (? list? xs) e)
       (define t (fresh-free!))
       (props-add! `(is-Proc ,t))
       (props-add! `(= (arity ,t) ,(length xs)))
       t]
      
      ;; Hacks for special applications go here
      [(-@ (-@ 'and/c ps _) es _)
       (define ts : (Listof Term) (for/list ([p ps]) (⦃e⦄! (-@ p es 0))))
       (define φ (-tand (for/list ([t ts]) `(is_truish ,t))))
       `(B ,φ)]
      [(-@ (-@ 'or/c ps _) es _)
       (define ts : (Listof Term) (for/list ([p ps]) (⦃e⦄! (-@ p es 0))))
       (define φ (-tor (for/list ([t ts]) `(is_truish ,t))))
       `(B ,φ)]
      [(-@ (-@ 'not/c (list p) _) es _)
       `(B (is_false ,(⦃e⦄! (-@ p es 0))))]
      [(-@ (-struct/c s cs _) es _)
       (define tₚ (⦃e⦄! (-@ (-st-p s) es 0)))
       (define ts : (Listof Term)
         (for/list ([(c i) (in-indexed cs)])
           (define eᵢ (-@ (-st-ac s (assert i exact-nonnegative-integer?)) es 0))
           (⦃e⦄! (-@ c (list eᵢ) 0))))
       (define φ (-tand (for/list ([t (cons tₚ ts)]) `(is_truish ,t))))
       `(B ,φ)]
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
          (props-add! `(and (,is-St ,@ts) (= (,tag ,@ts) ,stag)))]
         [_ (void)])
       
       (app-o o ts)]
      [(-@ eₕ eₓs _)
       (or
        (for/or : (Option Term) ([γ γs])
          (match-define (-γ τ bnd blm) γ)
          (match-define (-binding φₕ xs x->φ) bnd)
          (cond [(equal? eₕ (and φₕ (φ->e φₕ)))
                 (define fvs (set->list/memo (set-subtract (-binding-dom bnd) (list->seteq xs))))
                 (define tₐₚₚ (⦃app⦄! τ eₕ fvs xs eₓs))
                 (app-term! tₐₚₚ)]
                [else #f]))
        (begin
          #;(printf "Warning: can't find ~a among ~a~n"
                  (show-e e)
                  (for/list : (Listof Sexp) ([γ γs])
                    (match-define (-γ _ bnd _) γ)
                    (show-binding bnd)))
          (fresh-free!)))]
      [(? -->?)
       (define t (fresh-free!))
       (props-add! `(is-Arr ,t))
       t]
      [(? -->i?)
       (define t (fresh-free!))
       (props-add! `(is-ArrD ,t))
       t]
      [(? -struct/c?)
       (define t (fresh-free!))
       (props-add! `(is-St/C ,t))
       t]
      [_ (error '⦃e⦄! "unhandled: ~a" (show-e e))]))

  (: ⦃γ⦄! : -γ → Void)
  (define (⦃γ⦄! γ)
    (match-define (-γ τ bnd blm) γ)
    (define eₐₚₚ (binding->s bnd))
    (when eₐₚₚ
      (match-define (-binding _ xs _) bnd)
      (match-define (-@ eₕ eₓs _) eₐₚₚ)
      (define fvs (set->list/memo (set-subtract (-binding-dom bnd) (list->seteq xs))))
      (for ([fv fvs] #:unless (∋ bound fv)) (free-vars-add! (⦃x⦄ fv)))
      (define tₐₚₚ (⦃app⦄! τ eₕ fvs xs eₓs))
      (match blm
        [(cons l+ lo) (hash-set! asserts-app tₐₚₚ (cons (⦃l⦄ l+) (⦃l⦄ lo)))]
        [_            (hash-set! asserts-app tₐₚₚ #t)])))

  (for ([γ (reverse γs)]) (⦃γ⦄! γ))
  (for ([φ φs])
    (props-add! (tsimp (⦃e⦄! (φ->e φ)))))
  (define tₜₒₚ (⦃e⦄! e))
  (define all-props
    (∪ (for/set: : (℘ Formula) ([(tₐₚₚ res) asserts-app])
         (match res
           [#t `(is-Val ,tₐₚₚ)]
           [(? symbol? t) `(= ,tₐₚₚ (Val ,t))]
           [(cons l+ lo) `(= ,tₐₚₚ (Blm ,l+ ,lo))]))
       props))

  (values refs (Entry free-vars all-props tₜₒₚ)))



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

(: fun-name : -τ (Listof Var-Name) (Listof Var-Name) → Symbol)
(define fun-name
  (let ([m : (HashTable (List -τ (Listof Var-Name) (Listof Var-Name)) Symbol) (make-hash)])
    (λ (τ fvs xs)
      (hash-ref! m (list τ fvs xs) (λ () (format-symbol "f.~a" (hash-count m)))))))

(: ⦃o⦄ : -o → Symbol)
(define (⦃o⦄ o)
  (cond
    [(symbol? o) (format-symbol "o.~a" o)]
    [else (error '⦃o⦄ "unsupported: ~a" (show-o o))]))

(: o->id : -o → Integer)
(define o->id
  (let ([m : (HashTable -o Integer) (make-hash)])
    (λ (o) (hash-ref! m o (λ () (hash-count m))))))

(define ⦃sym⦄ : (Symbol → Integer)
  (let ([m : (HashTable Symbol Integer) (make-hasheq)])
    (λ (s) (hash-ref! m s (λ () (hash-count m))))))

(define ⦃str⦄ : (String → Integer)
  (let ([m : (HashTable String Integer) (make-hash)])
    (λ (s) (hash-ref! m s (λ () (hash-count m))))))

(: app-o : -o (Listof Term) → Term)
(define (app-o o ts)
  (case o
    [(defined?)
     `(B (not (is-Undefined ,@ts)))]
    [(number?)
     `(B (is-N ,@ts))]
    [(real?)
     `(B (is-R ,@ts))]
    [(integer?)
     `(B (is-Z ,@ts))]
    [(symbol?)
     `(B (is-Sym ,@ts))]
    [(string?)
     `(B (is-Str ,@ts))]
    [(procedure?)
     `(B (is-Proc ,@ts) #;(exists ([id Int]) (= ,@ts (Proc id))))]
    [(boolean?)
     `(B (is-B ,@ts))]
    [(vector?)
     `(B (is-Vec ,@ts))]
    [(not false?)
     (match ts
       [(list `(B (is_false ,t))) `(B (is_truish ,t))]
       [(list `(B (is_truish ,t))) `(B (is_false ,t))]
       [ts `(B (is_false ,@ts))])]
    [(null? empty?)
     `(B (= Null ,@ts))]
    [(procedure-arity)
     `(N (arity ,@ts) 0)]
    [(arity-includes?)
     (match-define (list a i) ts)
     `(B (= ,a ,i))]
    [(list)
     (foldr
      (λ ([tₗ : Term] [tᵣ : Term])
        `(St_2 ,(⦃struct-info⦄ -s-cons) ,tₗ ,tᵣ))
      'Null
      ts)]
    [(any/c) '(B true)]
    [(none/c) '(B false)]
    [(= equal?) `(B (= ,@ts))]
    [(< > <= >=)
     (match-define (list l r) ts)
     `(B (,(assert o symbol?) ,(N-real l) ,(N-real r)))]
    [(add1)
     (match-define (list t) ts)
     `(N (+ 1 ,(N-real t)) ,(N-imag t))]
    [(sub1)
     (match-define (list t) ts)
     `(N (- ,(N-real t) 1) ,(N-imag t))]
    [(+ -)
     (match-define (list x y) ts)
     `(N (,(assert o symbol?) ,(N-real x) ,(N-real y))
         (,(assert o symbol?) ,(N-imag x) ,(N-imag y)))]
    [(*)
     (match-define (list x y) ts)
     (define-values (a b c d) (values (N-real x) (N-imag x) (N-real y) (N-imag y)))
     `(N (- (* ,a ,c) (* ,b ,d))
         (+ (* ,a ,d) (* ,b ,c)))]
    [(/)
     (match-define (list x y) ts)
     (define-values (a b c d) (values (N-real x) (N-imag x) (N-real y) (N-imag y)))
     (define c²d² `(+ (* ,c ,c) (* ,d ,d)))
     `(N (/ (+ (* ,a ,c) (* ,b ,d)) ,c²d²)
         (/ (- (* ,b ,c) (* ,a ,d)) ,c²d²))]
    [(inexact?) `(B (inexact? ,@ts))]
    [(exact?) `(B (exact? ,@ts))]
    [(string-length) `(N (strlen ,@ts) 0)]
    [(and/c) `(And/C ,(next-int!))]
    [(or/c) `(Or/C ,(next-int!))]
    [(not/c) `(Not/C ,(next-int!))]
    [(vector-ref) `(f.vecref ,@ts)]
    [(vector-length) `(N (veclen ,@ts) 0)]
    [(list?) `(B (list? ,@ts))]
    [(map) `(f.map ,@ts)]
    [(append) `(f.append ,@ts)]
    [else
     (match o
       [(-st-p s)
        (define n (-struct-info-arity s))
        (define is-St (format-symbol "is-St_~a" n))
        (define st-tag (format-symbol "tag_~a" n))
        (define tag (⦃struct-info⦄ s))
        `(B (and (,is-St ,@ts) (= (,st-tag ,@ts) ,tag)))]
       [(-st-mk s)
        (define St (format-symbol "St_~a" (-struct-info-arity s)))
        `(,St ,(⦃struct-info⦄ s) ,@ts)]
       [(-st-ac s i)
        (define field (format-symbol "field_~a_~a" (-struct-info-arity s) i))
        `(,field ,@ts)]
       [_ (error 'app-o "unsupported: ~a" (show-o o))])]))

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

(: should-include-hack-for-is_int? : (℘ Term) → Boolean)
(define (should-include-hack-for-is_int? φs)
  (and (has-op? φs 'o.integer?)
       (for/or : Boolean ([o (in-list '(o.+ o.- o.*))])
         (has-op? φs o))))

(: has-op? : (℘ Term) Symbol → Boolean)
(define (has-op? φs o)

  (define go : (Term → Boolean)
    (match-lambda
      [(cons h t) (or (go h) (go t))]
      [s (equal? s o)]))

  (for/or : Boolean ([φ φs]) (go φ)))

(define N-real : (Term → Term)
  (match-lambda
    [`(N ,x ,_) x]
    [x `(real ,x)]))
(define N-imag : (Term → Term)
  (match-lambda
    [`(N ,_ ,y) y]
    [x `(imag ,x)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Emitting SMT2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: emit : (℘ Natural) Memo-Table Entry → (Values (Listof Sexp) Sexp))
;; Emit base and target to prove/refute
(define (emit struct-arities def-funs top)
  (match-define (Entry consts facts goal) top)

  (define emit-hack-for-is_int : (Listof Sexp)
    (cond [(should-include-hack-for-is_int? facts) hack-for-is_int]
          [else '()]))
  
  (define-values (emit-dec-funs emit-def-funs)
    (for/fold ([decs : (Listof Sexp) '()]
               [defs : (Listof Sexp) '()])
              ([(f-xs res) def-funs])
      (match-define (App τ fvs xs) f-xs)
      (define n (+ (length fvs) (length xs)))
      (define ⦃fv⦄s (map ⦃x⦄ fvs))
      (define tₓs (map ⦃x⦄ xs))
      (define fₕ (fun-name τ fvs xs))
      (define tₐₚₚ (-tapp fₕ ⦃fv⦄s tₓs))
      (match-define (Res oks ers) res)

      (: mk-cond : (Listof Entry) → Formula)
      (define (mk-cond entries)
        (match entries
          ['() 'false]
          [(list ent)
           (match-define (Entry xs facts _) ent)
           (-texists xs (-tand (set->list facts)))]
          [_
           (define-values (shared-xs shared-cond)
             (for/fold ([shared-xs : (℘ Symbol) (Entry-free-vars (first entries))]
                        [shared-cond : (℘ Term) (Entry-facts (first entries))])
                       ([ent (in-list (rest entries))])
               (match-define (Entry xs φs _) ent)
               (values (∩ shared-xs xs) (∩ shared-cond φs))))

           (define disjs
             (for/list : (Listof Term) ([ent entries])
               (match-define (Entry xs₀ φs₀ _) ent)
               (define xs (set-subtract xs₀ shared-xs))
               (define φs (set-subtract φs₀ shared-cond))
               (-texists xs (-tand (set->list φs)))))

           (-texists shared-xs (-tand `(,@(set->list shared-cond) ,(-tor disjs))))]))

      (define ok-cond (mk-cond oks))
      (define er-cond (mk-cond ers))
      (define params
        (append (for/list : (Listof Sexp) ([⦃fv⦄ ⦃fv⦄s]) `(,⦃fv⦄ V))
                (for/list : (Listof Sexp) ([x tₓs]) `(,x V))))

      (: assrt : (Listof Sexp) Sexp → Sexp)
      (define (assrt params cnd)
        `(assert
          ,(cond
             [(null? params) cnd]
             [else `(forall ,params (! ,cnd :pattern (,tₐₚₚ)))])))
      
      (values
       (cons `(declare-fun ,fₕ ,(make-list n 'V) A) decs)
       (list*
        ;; For each function, generate implications from returns and blames
        (assrt params `(=> (is-Val ,tₐₚₚ) ,ok-cond))
        (assrt params `(=> (is-Blm ,tₐₚₚ) ,er-cond))
        defs))))

  (define emit-dec-consts : (Listof Sexp) (for/list ([x consts]) `(declare-const ,x V)))
  (define emit-asserts : (Listof Sexp) (for/list ([φ facts]) `(assert ,φ)))

  (values `(,@(SMT-base struct-arities)
            ,@emit-hack-for-is_int
            ,@emit-dec-consts
            ,@emit-dec-funs
            ,@emit-def-funs
            ,@emit-asserts)
          goal))

(: base-datatypes : (℘ Natural) → (Listof Sexp))
(define (base-datatypes arities)
  (define st-defs : (Listof Sexp)
    (for/list ([n (set-add arities #|hack|# 2)])
      (define St_k (format-symbol "St_~a" n))
      (define tag_k (format-symbol "tag_~a" n))
      (define fields : (Listof Sexp) (for/list ([i n]) `(,(format-symbol "field_~a_~a" n i) V)))
      `(,St_k (,tag_k Int) ,@fields)))
  
  `(;; Unitype
    (declare-datatypes ()
      ((V ; TODO
        Undefined
        Null
        (N [real Real] [imag Real])
        (B [unbox_B Bool])
        (Proc [proc_id Int])
        (Sym [sym Int])
        (Str [str Int])
        (And/C [and/c_id Int])
        (Or/C [or/c_id Int])
        (Not/C [not/c_id Int])
        (St/C [unbox_st/c Int])
        (Arr [unbox_Arr Int])
        (ArrD [unbox_ArrD Int])
        (Vec [unbox_Vec Int])
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
  `(;; Primitive predicates
    (define-fun is_false ([x V]) Bool
      (= x (B false)))
    (define-fun is_truish ([x V]) Bool
      (not (is_false x)))
    (define-fun is-R ([x V]) Bool
      (and (is-N x) (= 0 (imag x))))
    (define-fun is-Z ([x V]) Bool
      (and (is-R x) (is_int (real x))))
    (declare-fun exact? (V) Bool)
    (declare-fun inexact? (V) Bool)
    (declare-fun strlen (V) Int)
    (declare-fun f.vecref (V V) V)
    (declare-fun veclen (V) Int)
    (assert (forall ((v V)) (>= (strlen v) 0)))
    (assert (forall ((v V)) (>= (veclen v) 0)))
    (declare-fun arity (V) Int)
    (assert (forall ((v V)) (>= (arity v) 0)))
    (declare-fun list? (V) Bool)
    (assert (list? Null))
    (assert (forall ([h V] [t V])
                    (=> (list? t) (list? (St_2 ,(⦃struct-info⦄ -s-cons) h t)))))
    (declare-fun f.map (V V) V)
    (declare-fun f.append (V V) V)
    ))

(define hack-for-is_int : (Listof Sexp)
  '{(assert (forall ([x Real] [y Real])
              (=> (and (is_int x) (is_int y)) (is_int (+ x y)))))
    (assert (forall ([x Real] [y Real])
              (=> (and (is_int x) (is_int y)) (is_int (- x y)))))
    (assert (forall ([x Real] [y Real])
              (=> (and (is_int x) (is_int y)) (is_int (* x y)))))
    })


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(: -texists : (℘ Symbol) Term → Term)
(define (-texists xs t)
  (cond
    [(set-empty? xs) t]
    [else `(exists ,(for/list : (Listof Sexp) ([x xs]) `(,x V)) ,t)]))

(: -tapp : Term (Listof Symbol) (Listof Term) → Term)
(define (-tapp f fvs xs) (if (and (null? fvs) (null? xs)) f `(,f ,@fvs ,@xs)))

(: tsimp : Term → Sexp)
(define (tsimp t)
  (match t
    [`(B (is_false (B ,φ))) `(not ,φ)]
    [`(B (is_truish (B ,φ))) φ]
    [`(B ,φ) φ]
    [_ `(is_truish ,t)]))

;; memoize to ensure fixed order
(define/memo (set->list/memo [xs : (Setof Var-Name)]) : (Listof Var-Name) (set->list xs))

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
