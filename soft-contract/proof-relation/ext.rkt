#lang typed/racket/base

(provide external-prover@)

(require racket/match
         racket/set
         racket/list
         racket/splicing
         (only-in z3/ffi toggle-warning-messages!)
         typed/racket/unit
         z3/smt
         bnf
         intern
         set-extras
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "../signatures.rkt")

(define-interner ⦃o⦄ -o #:intern-function-name -o->⦃o⦄)
(define-interner ⦃Symbol⦄ Symbol #:intern-function-name Symbol->⦃Symbol⦄)
(define-interner ⦃String⦄ String #:intern-function-name String->⦃String⦄)
(define-interner ⦃Char⦄ Char #:intern-function-name Char->⦃Char⦄)
(define-interner ⦃l⦄ -l #:intern-function-name -l->⟪l⟫)
(define-interner ⦃𝒾⦄ -𝒾 #:intern-function-name -𝒾->⦃𝒾⦄)

;; TODO I should have used reader monad for z3/smt instead of this hack
(define-type (M T) (→ T))

;; Translation context
(struct Ctx ([bound : (℘ Symbol)] [cache : (HashTable -t (M Z3-Ast))]) #:transparent)

(define-unit external-prover@
  (import for-gc^ pretty-print^ pc^ sto^)
  (export external-prover^)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; For-Translate
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: ret (∀ (α) α → (M α)))
  (define (ret v) (λ () v))

  (: >>= (∀ (α β) (M α) (α → (M β)) → (M β)))
  (define ((a . >>= . mb)) ((mb (a))))

  (define-syntax do
    (syntax-rules (← ≔ :)
      [(_ m) m]
      [(_ [p : τ ← m₁] m ...) (m₁ . >>= . (λ ([x : τ])
                                            (match-define p x)
                                            (do m ...)))]
      [(_ [p ≔ e ] m ...) (match-let ([p e]) (do m ...))]
      [(_  m₁      m ...) (m₁ . >>= . (λ _ (do m ...)))]))

  (: iter-M : (Sequenceof (M Void)) → (M Void))
  (define ((iter-M ms)) (for ([m ms]) (m)))

  (: list-M (∀ (α) (Listof (M α)) → (M (Listof α))))
  (define ((list-M ms))
    (for/list : (Listof α) ([m (in-list ms)]) (m)))

  (: assert-M : (M Z3-Ast) → (M Void))
  (define ((assert-M t)) (assert! (t)))

  (: run (∀ (α) (M α) → α))
  (define (run m)
    (with-new-context (m)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Translation
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: ⦃Γ⦄ : Ctx -Γ → (Values (℘ (M Z3-Ast)) (℘ Symbol)))
  ;; Translate path condition into a set of Z3 computation each returning an AST of sort Bool
  ;; along with the set of generated free variables
  (define (⦃Γ⦄ ctx Γ)
    (define-set fvs : Symbol #:eq? #t)
    (define ⦃φ⦄s
      (for/unioneq : (℘ (M Z3-Ast)) ([φ (in-set Γ)])
                   (define-values (props fvs*) (⦃φ⦄ ctx φ))
                   (fvs-union! fvs*)
                   props))
    (values ⦃φ⦄s fvs))

  (: ⦃φ⦄ : Ctx -t → (Values (℘ (M Z3-Ast)) (℘ Symbol)))
  ;; Translate proposition `φ` into:
  ;; - Z3 computations each returning AST of sort Bool (interpreted as conjunction)
  ;; - set of free variables generated
  (define (⦃φ⦄ ctx φ)
    (define-values (res cnds fvs) (⦃t⦄ ctx φ))
    (values
     (set-add cnds
              (λ () (not/s (=/s (res) (@/s 'B false/s)))))
     fvs))

  (: ⦃t⦄ : Ctx -t → (Values (M Z3-Ast) (℘ (M Z3-Ast)) (℘ Symbol)))
  ;; Translate term into:
  ;; - Z3 computation that return Z3 term of sort `V`,
  ;; - Z3 computation that return Z3 terms of sort `B` that must be true (as preconditions)
  ;; - set of generated free variables.
  ;; The reason the set of free variables is not part of the computation
  ;; is because they are meant to be either declared or abstracted over.
  (define (⦃t⦄ ctx t)
    (define-set free-vars : Symbol #:eq? #t)
    (define-set preconds : (M Z3-Ast) #:eq? #t)

    (: fresh-free! : Symbol → Symbol)
    (define (fresh-free! prefix)
      (hash-update! fresh-ids prefix add1 (λ () 0))
      (define i (hash-ref fresh-ids prefix))
      (define x (format-symbol "~a.~a" prefix i))
      (free-vars-add! x)
      x)

    (define (go! [t : -t]) : (M Z3-Ast)
      (hash-ref!
       (Ctx-cache ctx)
       t
       (λ ()
         (match t
           [(? integer? ℓ₀)
            (define t (⦃ℓ⦄ (cast ℓ₀ ℓ)))
            (free-vars-add! t)
            (λ () (val-of t))]
           [(-t.x x)
            (define t (⦃x⦄ x))
            (unless (∋ (Ctx-bound ctx) x)
              (free-vars-add! t))
            (λ () (val-of t))]
           [(? -𝒾? 𝒾)
            (define t (⦃ref⦄ 𝒾))
            (free-vars-add! t)
            (λ () (val-of t))]
           [(-b b) (⦃b⦄ b)]
           [(? -o? o)
            (define id (-o->⦃o⦄ o))
            (λ () (@/s 'Proc id))]
           [(-λ xs e)
            (define t (fresh-free! 'lam))
            (preconds-add! (λ () (@/s 'is-Proc t)))
            (λ () (val-of t))]
           [(-t.@ h ts) (go-@! h (map go! ts))]))))

    (: go-@! : -h (Listof (M Z3-Ast)) → (M Z3-Ast))
    (define (go-@! h ⦃t⦄s)
      (match h
        [(? -o? h)
         (or (⦃prim⦄ h ⦃t⦄s)
             (let ([t (fresh-free! 'prim-app)])
               (λ () (val-of t))))]
        [(-One-Of/C bs)
         (define ⦃b⦄s (set-map bs ⦃b⦄))
         (λ ()
           (match-define (list t) ((list-M ⦃t⦄s)))
           (@/s 'B (or/s/simp (for/list : (Listof Z3-Ast) ([bᵢ (in-list ((list-M ⦃b⦄s)))])
                                (=/s t bᵢ)))))]
        [(-≥/c (? real? b))
         (λ ()
           (match-define (list t) ((list-M ⦃t⦄s)))
           (@/s 'B (>=/s (@/s 'real t) b)))]
        [(-≤/c (? real? b))
         (λ ()
           (match-define (list t) ((list-M ⦃t⦄s)))
           (@/s 'B (<=/s (@/s 'real t) b)))]
        [(-</c (? real? b))
         (λ ()
           (match-define (list t) ((list-M ⦃t⦄s)))
           (@/s 'B (</s (@/s 'real t) b)))]
        [(->/c (? real? b))
         (λ ()
           (match-define (list t) ((list-M ⦃t⦄s)))
           (@/s 'B (>/s (@/s 'real t) b)))]
        [_
         (warn-unsupported h)
         (define t (fresh-free! 'unhandled))
         (λ () (val-of t))]))

    (define res (go! t))
    (hash-set! (Ctx-cache ctx) t res)
    (values res preconds free-vars))

  (: ⦃prim⦄ : -o (Listof (M Z3-Ast)) → (Option (M Z3-Ast)))
  ;; Return computation that returns Z3-Ast of sort `V`
  (define (⦃prim⦄ o ⦃t⦄s)
    (case o
      [(defined?)
       (λ () (@/s 'B (not/s (=/s 'Undefined ((car ⦃t⦄s))))))]
      [(number?)
       (λ () (@/s 'B (@/s 'is-N ((car ⦃t⦄s)))))]
      [(real?)
       (λ () (@/s 'B (@/s 'is-R ((car ⦃t⦄s)))))]
      [(integer?)
       (λ () (@/s 'B (@/s 'is-Z ((car ⦃t⦄s)))))]
      [(symbol?)
       (λ () (@/s 'B (@/s 'is-Sym ((car ⦃t⦄s)))))]
      [(string?)
       (λ () (@/s 'B (@/s 'is-Str ((car ⦃t⦄s)))))]
      [(procedure?)
       (λ () (@/s 'B (@/s 'is-Proc ((car ⦃t⦄s)))))]
      [(boolean?)
       (λ () (@/s 'B (@/s 'is-B ((car ⦃t⦄s)))))]
      [(void?)
       (λ () (@/s 'B (=/s 'Void ((car ⦃t⦄s)))))]
      [(vector)
       (define i (next-int!))
       (λ () (@/s 'Vec i))]
      [(vector?)
       (λ () (@/s 'B (@/s 'is-Vec ((car ⦃t⦄s)))))]
      [(not false?)
       (λ () (@/s 'B (=/s ((car ⦃t⦄s)) (@/s 'B false/s))))]
      [(null? empty?)
       (λ () (@/s 'B (=/s 'Null ((car ⦃t⦄s)))))]
      [(procedure-arity)
       (λ () (@/s 'N (@/s 'arity ((car ⦃t⦄s))) 0))]
      [(arity-includes?)
       (match-define (list a i) ⦃t⦄s)
       (λ () (@/s 'B (=/s (a) (i))))]
      [(list)
       (λ ()
         (foldr
          (λ ([tₗ : Z3-Ast] [tᵣ : Z3-Ast])
            (@/s 'St_2 (-𝒾->⦃𝒾⦄ -𝒾-cons) tₗ tᵣ))
          (val-of 'Null)
          (for/list : (Listof Z3-Ast) ([t ⦃t⦄s]) (t))))]
      [(any/c) (λ () (@/s 'B true/s))]
      [(none/c) (λ () (@/s 'B false/s))]
      [(= equal? eq?)
       (match-define (list t₁ t₂) ⦃t⦄s)
       (λ () (@/s 'B (=/s (t₁) (t₂))))]
      [(< > <= >=)
       (match-define (list l r) ⦃t⦄s)
       (define o/s : (Z3-Ast Z3-Ast → Z3-Ast)
         (case o
           [(<) </s]
           [(<=) <=/s]
           [(>) >/s]
           [else >=/s]))
       (λ ()
         (@/s 'B (o/s (@/s 'real (l)) (@/s 'real (r)))))]
      [(add1)
       (match-define (list t) ⦃t⦄s)
       (λ ()
         (@/s 'N (+/s 1 (@/s 'real (t))) (@/s 'imag (t))))]
      [(sub1)
       (match-define (list t) ⦃t⦄s)
       (λ ()
         (@/s 'N (-/s (@/s 'real (t)) 1) (@/s 'imag (t))))]
      [(+ -)
       (match-define (list x y) ⦃t⦄s)
       (define o/s : (Smt-Expr Smt-Expr → Z3-Ast)
         (case o
           [(+) +/s]
           [else -/s]))
       (λ ()
         (@/s 'N
              (o/s (@/s 'real (x)) (@/s 'real (y)))
              (o/s (@/s 'imag (x)) (@/s 'imag (y)))))]
      [(*)
       (match-define (list x y) ⦃t⦄s)
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
       (match-define (list x y) ⦃t⦄s)
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
       (λ ()
         (@/s 'N (^/s (@/s 'real ((car ⦃t⦄s))) 0.5) 0))]
      [(zero?)
       (match-define (list t) ⦃t⦄s)
       (λ ()
         (@/s 'B (=/s (@/s 'N 0 0) (t))))]
      [(positive?)
       (λ ()
         (define tₐ ((car ⦃t⦄s)))
         (@/s 'B
              (and/s (@/s 'is-R tₐ)
                     (>/s (@/s 'real tₐ) 0))))]
      [(negative?)
       (λ ()
         (define tₐ ((car ⦃t⦄s)))
         (@/s 'B
              (and/s (@/s 'is-R tₐ)
                     (</s (@/s 'real tₐ) 0))))]
      [(exact-integer?)
       (λ ()
         (define tₐ ((car ⦃t⦄s)))
         (@/s 'B (and/s (@/s 'is-Z tₐ) (@/s 'exact? tₐ))))]
      [(exact-nonnegative-integer?)
       (λ ()
         (define tₐ ((car ⦃t⦄s)))
         (@/s 'B (and/s (@/s 'is-Z tₐ)
                        (@/s 'exact? tₐ)
                        (>=/s (@/s 'real tₐ) 0))))]
      [(exact-positive-integer?)
       (λ ()
         (define tₐ ((car ⦃t⦄s)))
         (@/s 'B (and/s (@/s 'is-Z tₐ)
                        (@/s 'exact? tₐ)
                        (>/s (@/s 'real tₐ) 0))))]
      ;; HERE
      [(inexact?)
       (λ ()
         (@/s 'B (@/s 'inexact? ((car ⦃t⦄s)))))]
      [(exact?)
       (λ ()
         (@/s 'B (@/s 'exact? ((car ⦃t⦄s)))))]
      [(string-length)
       (λ ()
         (@/s 'N (@/s 'strlen ((car ⦃t⦄s))) 0))]
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
       (match-define (list t₁ t₂) ⦃t⦄s)
       (λ () (@/s 'f.vecref (t₁) (t₂)))]
      [(vector-length)
       (λ () (@/s 'N (@/s 'veclen ((car ⦃t⦄s))) 0))]
      [(list?)
       (λ () (@/s 'B (@/s 'list? ((car ⦃t⦄s)))))]
      [(map)
       (match-define (list t₁ t₂) ⦃t⦄s)
       (λ () (@/s 'f.map (t₁) (t₂)))]
      [(append)
       (match-define (list t₁ t₂) ⦃t⦄s)
       (λ () (@/s 'f.append (t₁) (t₂)))]
      [(min)
       (match-define (list t₁ t₂) ⦃t⦄s)
       (λ () (@/s 'N (@/s 'f.min (@/s 'real (t₁)) (@/s 'real (t₂))) 0))]
      [(max)
       (match-define (list t₁ t₂) ⦃t⦄s)
       (λ () (@/s 'N (@/s 'f.max (@/s 'real (t₁)) (@/s 'real (t₂))) 0))]
      [else
       (match o
         [(-st-p 𝒾)
          (define n (get-struct-arity 𝒾))
          (define is-St (format-symbol "is-St_~a" n))
          (define st-tag (format-symbol "tag_~a" n))
          (match-define (list t) ⦃t⦄s)
          (λ ()
            (define tₐ (t))
            (@/s 'B (and/s (@/s is-St tₐ)
                           (=/s (@/s st-tag tₐ) (-𝒾->⦃𝒾⦄ 𝒾)))))]
         [(-st-mk 𝒾)
          (define St (format-symbol "St_~a" (get-struct-arity 𝒾)))
          (λ ()
            (apply @/s St (-𝒾->⦃𝒾⦄ 𝒾) ((list-M ⦃t⦄s))))]
         [(-st-ac 𝒾 i)
          (define field (format-symbol "field_~a_~a" (get-struct-arity 𝒾) i))
          (λ () (@/s field ((car ⦃t⦄s))))]
         [_
          (warn-unsupported o)
          #f])]))

  (: ⦃b⦄ : Base → (M Z3-Ast))
  (define (⦃b⦄ b)
    (match b
      [#f (λ () (@/s 'B false/s))]
      [#t (λ () (@/s 'B true/s))]
      [(? number? x) (λ () (@/s 'N (real-part x) (imag-part x)))]
      [(? symbol? s) (λ () (@/s 'Sym (Symbol->⦃Symbol⦄ s)))]
      [(? string? s) (λ () (@/s 'Str (String->⦃String⦄ s)))]
      [(? void?) (λ () (val-of 'Void))]
      [(? char? c) (λ () (@/s 'Chr (Char->⦃Char⦄ c)))]
      [(list) (λ () (val-of 'Null))]
      [(? eof-object? b) (λ () (val-of 'EOF))]
      [_ (error '⦃b⦄ "value: ~a" b)]))

  (: assert-true! : Z3-Ast → (M Void))
  (define ((assert-true! t))
    (assert! (not/s (=/s t (@/s 'B false/s)))))

  (: assert-false! : Z3-Ast → (M Void))
  (define ((assert-false! t))
    (assert! (=/s t (@/s 'B false/s))))

  (: declare-consts : (Sequenceof Symbol) Smt-Sort-Expr → (M Void))
  (define ((declare-consts xs t))
    (void (for ([x xs])
            (dynamic-declare-const x t))))

  (: define-base-datatypes : (℘ Natural) → (M Void))
  (define (define-base-datatypes arities)
    (λ ()
      (define st-defs : (Listof (Pairof Symbol (Listof (List Symbol Smt-Sort-Expr))))
        (for/list ([n arities])
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
         EOF
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
       None)))

  (: define-base-predicates : (℘ -o) → (M Void))
  ;; Define base predicates, parameterized by actually used primitives to reduce query size
  (define (define-base-predicates prims)

    (define-set other-cmds : (M Void) #:eq? #t #:as-mutable-hash? #t)
    (define-syntax-rule (with-condition! p e ...)
      (when p
        (other-cmds-add! (λ () e ...))))

    (with-condition! (not (set-empty? (∩ prims (set 'exact? 'exact-integer? 'exact-nonnegative-integer? 'exact-positive-integer?))))
      (dynamic-declare-fun 'exact? '(V) Bool/s)
      (void))
    
    (with-condition! (∋ prims 'inexact?)
      (dynamic-declare-fun 'inexact? '(V) Bool/s)
      (void))
    
    (with-condition! (∋ prims 'string-length)
      (dynamic-declare-fun 'strlen '(V) Int/s)
      (assert! (∀/s ([v 'V]) (>=/s (@/s 'strlen v) 0))))

    (with-condition! (∋ prims 'vector-ref)
      (dynamic-declare-fun 'f.vecref '(V V) 'V)
      (void))
    
    (with-condition! (∋ prims 'vector-length)
      (dynamic-declare-fun 'veclen '(V) Int/s)
      (assert! (∀/s ([v 'V]) (>=/s (@/s 'veclen v) 0))))

    (with-condition! #t #;(∋ prims 'procedure-arity)
      (dynamic-declare-fun 'arity '(V) Int/s)
      (assert! (∀/s ([v 'V]) (>=/s (@/s 'arity v) 0))))
    
    (with-condition! (∋ prims 'list?)
      (dynamic-declare-fun 'list? '(V) Bool/s)
      (assert! (@/s 'list? 'Null))
      (assert! (∀/s ([h 'V] [t 'V])
                    (=>/s (@/s 'list? t) (@/s 'list? (@/s 'St_2 (-𝒾->⦃𝒾⦄ -𝒾-cons) h t))))))

    (with-condition! (∋ prims 'map)
      (dynamic-declare-fun 'f.map '(V V) 'V)
      (void))
    
    (with-condition! (∋ prims 'append)
      (dynamic-declare-fun 'f.append '(V V) 'V)
      (void))

    (with-condition! (∋ prims 'min)
      (dynamic-define-fun 'f.min ([x Real/s] [y Real/s]) Real/s (ite/s (<=/s x y) x y)))
    
    (with-condition! (∋ prims 'max)
      (dynamic-define-fun 'f.max ([x Real/s] [y Real/s]) Real/s (ite/s (>=/s x y) x y)))

    (λ ()
      (define-fun is-R ([x 'V]) Bool/s
        (and/s (@/s 'is-N x) (=/s 0 (@/s 'imag x))))
      (define-fun is-Z ([x 'V]) Bool/s
        (and/s (@/s 'is-R x) (is-int/s (@/s 'real x))))
      ;; Other optional ones
      (for ([cmd (in-other-cmds)])
        (cmd))))

  (: collect-usage : (U -Γ -t) * → (Values (℘ Natural) (℘ -o)))
  (define (collect-usage . xs)
    (define-set arities : Natural #:eq? #t)
    (define-set prims   : -o)

    (: go-A! : -A → Void)
    (define go-A!
      (match-lambda
        [(-W _ t) #:when t (go-t! t)]
        [_ (void)]))

    (: go-Γ! : -Γ → Void)
    (define (go-Γ! Γ) (set-for-each Γ go-t!))

    (: go-t! : -t → Void)
    (define go-t!
      (match-lambda
        [(-t.@ h ts) (go-h! h) (for-each go-t! ts)]
        [_ (void)]))

    (: go-h! : -h → Void)
    (define go-h!
      (match-lambda
        [(? -o? o)
         (prims-add! o)
         (match o
           [(or (-st-mk 𝒾) (-st-p 𝒾) (-st-ac 𝒾 _) (-st-mut 𝒾 _)) #:when 𝒾
            (arities-add! (get-struct-arity 𝒾))]
           [_ (void)])]
        [(or (-st/c.mk 𝒾) (-st/c.ac 𝒾 _)) #:when 𝒾
         (arities-add! (get-struct-arity 𝒾))]
        [_ (void)]))

    (for ([x (in-list xs)])
      (cond [(set? x) (go-Γ! x)]
            [else (go-t! x)]))

    (values (∪ #|HACK|# {seteq 1 2} arities) prims))

  (: ⦃ℓ⦄ : ℓ → Symbol)
  (define (⦃ℓ⦄ ℓ)
    (format-symbol "loc.~a" ℓ))

  (: ⦃x⦄ : Symbol → Symbol)
  (define (⦃x⦄ x)
    (string->symbol (adjust-name (symbol->string x))))

  ;; Part of a hack
  (define refs : (℘ Symbol) {seteq})

  (: ⦃ref⦄ : -𝒾 → Symbol)
  (define (⦃ref⦄ 𝒾)
    (define x (format-symbol "ref.~a" (string->symbol (adjust-name (symbol->string (-𝒾-name 𝒾))))))
    (set! refs (set-add refs x))
    x)

  (: adjust-name : String → String)
  (define (adjust-name s)

    (: subst : Char → (Listof Char))
    (define (subst c)
      ; TODO this is prone to error if there's `x_0` in original program
      (case c
        [(#\₀) '(#\_ #\0)]
        [(#\₁) '(#\_ #\1)]
        [(#\₂) '(#\_ #\2)]
        [(#\₃) '(#\_ #\3)]
        [(#\₄) '(#\_ #\4)]
        [(#\₅) '(#\_ #\5)]
        [(#\₆) '(#\_ #\6)]
        [(#\₇) '(#\_ #\7)]
        [(#\₈) '(#\_ #\8)]
        [(#\₉) '(#\_ #\9)]
        [(#\⁰) '(#\^ #\0)]
        [(#\¹) '(#\^ #\1)]
        [(#\²) '(#\^ #\2)]
        [(#\³) '(#\^ #\3)]
        [(#\⁴) '(#\^ #\4)]
        [(#\⁵) '(#\^ #\5)]
        [(#\⁶) '(#\^ #\6)]
        [(#\⁷) '(#\^ #\7)]
        [(#\⁸) '(#\^ #\8)]
        [(#\⁹) '(#\^ #\9)]
        [(#\:) '(#\_)]
        [else (list c)]))

    (list->string (append-map subst (string->list s))))

  (: next-int! : → Natural)
  (define next-int!
    (let ([i : Natural 0])
      (λ ()
        (begin0 i (set! i (+ 1 i))))))

  (define fresh-ids : (HashTable Symbol Natural) (make-hasheq))

  ;; This table is just for printing out each warning once
  (define warn-unsupported : (-h → Void)
    (let ([m : (HashTable -h Void) (make-hash)])
      (λ (h)
        (hash-ref! m h
                   (λ ()
                     (printf "warning: existentialize result for unmapped `~a`~n" (show-h h)))))))

  (: and/s/simp : (Listof Z3-Ast) → Z3-Ast)
  (define (and/s/simp clauses)
    (match clauses
      ['() true/s]
      [(list clause) clause]
      [_ (apply and/s clauses)]))

  (: or/s/simp : (Listof Z3-Ast) → Z3-Ast)
  (define (or/s/simp clauses)
    (match clauses
      ['() false/s]
      [(list clause) clause]
      [_ (apply or/s clauses)]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Use
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (toggle-warning-messages! #f)

  ;; TODO use `define/memo` once Typed Unit is fixed
  (define/memo (ext-prove [Γ : -Γ] [t : -t]) : -R
    (define (set-default-options!)
      (set-options! #:timeout (assert (estimate-time-limit Γ t) fixnum?)
                    #:mbqi? #t
                    #:macro-finder? #t
                    #:rlimit 4000000))

    (define-values (st-arities prims) (collect-usage Γ t))
    (define-values (do-Γ cnds do-t fvs)
      (let ([ctx₀ (Ctx ∅eq (make-hash))])
        (define-values (do-Γ      fvs-Γ) (⦃Γ⦄ ctx₀ Γ))
        (define-values (do-t cnds fvs-t) (⦃t⦄ ctx₀ t))
        (values do-Γ cnds do-t (∪ fvs-Γ fvs-t))))
    (define-values (globals locals) (values (∩ fvs refs) (set-subtract fvs refs)))
    (define do-base
      (do set-default-options!
          (define-base-datatypes st-arities)
        (define-base-predicates prims)
        (declare-consts globals 'V)
        (declare-consts locals 'V)
        (iter-M (set-map do-Γ assert-M))
        (iter-M (set-map cnds assert-M))))
    
    ;; TODO: Z3's incremental solver eats of memory and locks up my computer
    ;; if query has `is_int`, so I'm running 2 fresh queries worst case here.
    (with-debugging/off ((R) (case (run (do
                                            do-base
                                            (assert-false! (do-t))
                                          #;(λ ()
                                              (print-current-assertions)
                                              (printf "check false~n~n"))
                                          check-sat))
                               [(unsat) '✓]
                               [(sat unknown)
                                (case (run (do
                                               do-base
                                               (assert-true! (do-t))
                                             #;(λ ()
                                                 (print-current-assertions)
                                                 (printf "check true~n~n"))
                                             check-sat))
                                  [(unsat) '✗]
                                  [(sat unknown) '?])]))
      (printf "  --> ~a~n~n" R)))

  (define (estimate-time-limit [Γ : -Γ] [t : -t]) : Natural
    (* (set-count Γ) 3))
)
