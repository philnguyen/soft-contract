#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/splicing
         racket/set
         racket/bool
         typed/racket/unit
         "../utils/list.rkt"
         "signatures.rkt")

(define-unit ast-macros@
  (import meta-functions^ static-info^)
  (export ast-macros^)

  (: -define : Symbol -e ℓ → -define-values)
  (define (-define x e ℓ) (-define-values (list x) e ℓ))

  (: -cond : (Assoc -e -e) -e ℓ → -e)
  (define (-cond cases default ℓ)
    (foldr (λ ([alt : (Pairof -e -e)] [els : -e])
             (match-define (cons cnd thn) alt)
             (-if cnd thn els ℓ))
           default
           cases))

  (: --> ([(-var -e) -e ℓ] [#:total? (Option ℓ)] . ->* . -->i))
  (define (--> doms rng ℓ #:total? [total? #f])
    (define (gen-dom [c : -e])
      (define x (gensym '_))
      (-dom x #f c (ℓ-with-id ℓ x)))
    (-->i (var-map gen-dom doms) (list (gen-dom rng)) total?))

  ;; Make conjunctive and disjunctive contracts
  (splicing-local
      ((: -app/c : Symbol → (Assoc ℓ -e) → -e)
       (define ((-app/c o) args)
         (let go ([args : (Assoc ℓ -e) args])
           (match args
             ['() 'any/c]
             [(list (cons ℓ e)) e]
             [(cons (cons ℓ e) args*) (-@ o (list e (go args*)) ℓ)]))))
    (define -and/c (-app/c 'and/c))
    (define -or/c (-app/c 'or/c)))

  (: -cons/c : -e -e ℓ → -e)
  (define (-cons/c c d ℓ)
    (-@ 'scv:struct/c (list -cons c d) ℓ))

  (: -box/c : -e ℓ → -e)
  (define (-box/c c ℓ)
    (-@ 'scv:struct/c (list -box c) ℓ))

  (: -list/c : (Assoc ℓ -e) → -e)
  (define (-list/c args)
    (foldr (λ ([arg : (Pairof ℓ -e)] [acc : -e])
             (match-define (cons ℓ e) arg)
             (-cons/c e acc ℓ))
           'null?
           args))

  (: -list : (Assoc ℓ -e) → -e)
  (define (-list args)
    (match args
      ['() -null]
      [(cons (cons ℓ e) args*)
       (-@ -cons (list e (-list args*)) (ℓ-with-id ℓ 'list))]))

  (: -list* : (Assoc ℓ -e) -e → -e)
  (define (-list* args tail)
    (foldr (λ ([i : (Pairof ℓ -e)] [ac : -e]) (-@ -cons (list (cdr i) ac) (car i)))
           tail
           args))

  (: -and : (Listof -e) ℓ → -e)
  ;; Return ast representing conjuction of 2 expressions
  (define (-and es ℓ)
    (match es
      [(list) -tt]
      [(list e) e]
      [(cons e es) (-if e (-and es ℓ) -ff ℓ)]))

  (: -comp/c : Symbol -e ℓ → -e)
  ;; Return ast representing `(op _ e)`
  (define (-comp/c op e ℓ)
    (define x (-x 'cmp (ℓ-with-id ℓ 'cmp)))
    (match-define (list ℓ₀ ℓ₁) (ℓ-with-ids ℓ 2))
    (-λ (-var '(cmp) #f)
        (-and (list (-@ 'real? (list x) ℓ₀)
                    (-@ op (list x e) ℓ₁))
              ℓ)
        (ℓ-with-id ℓ 'lam)))

  (: -begin/simp : (∀ (X) (Listof X) → (U X (-begin X))))
  ;; Smart constructor for begin, simplifying single-expression case
  (define/match (-begin/simp xs)
    [((list e)) e]
    [(es) (-begin es)])

  (: -begin0/simp : -e (Listof -e) → -e)
  (define (-begin0/simp e es)
    (if (null? es) e (-begin0 e es)))

  (: -@/simp : -e (Listof -e) ℓ → -e)
  (define -@/simp
    (match-lambda**
     [('values (list x) _) x]
     [('not (list (-b b)) _) (-b (not b))]
     [((-λ (-var (? list? xs) #f) e _) es ℓ)
      #:when (= (length xs) (length es))
      (-let-values/simp
       (for/list ([x (in-list xs)] [e (in-list es)])
         (cons (list x) e))
       e
       ℓ)]
     [(f xs ℓ) (-@ f xs ℓ)]))

  (: -let-values/simp : (Assoc (Listof Symbol) -e) -e ℓ → -e)
  (define -let-values/simp
    (match-lambda**
     [('() e _) e]
     [((list (cons (list x) eₓ)) (-x x _) _) eₓ]
     [((and bindings (list (cons (list lhss) rhss) ...)) body ℓ)
      (define-values (bindings-rev inlines)
        (for/fold ([bindings-rev : (Assoc (Listof Symbol) -e) '()]
                   [inlines : Subst (hasheq)])
                  ([lhs (in-list lhss)]
                   [rhs (in-list rhss)]
                   #:when (and (symbol? lhs) (-e? rhs)))
          (if (inlinable? lhs rhs body)
              (values bindings-rev (hash-set inlines lhs rhs))
              (values (cons (cons (list lhs) rhs) bindings-rev) inlines))))
      (cond [(hash-empty? inlines)
             (-let-values bindings body ℓ)]
            [(null? bindings-rev)
             (e/map inlines body)]
            [else
             (-let-values (reverse bindings-rev) (e/map inlines body) ℓ)])]
     [(bindings body ℓ) (-let-values bindings body ℓ)]))

  (: -if/simp : -e -e -e ℓ → -e)
  (define -if/simp
    (match-lambda**
     [((-b #f) _ e _) e]
     [((-b _ ) e _ _) e]
     [(i t e ℓ) (-if i t e ℓ)]))

  (: inlinable? : Symbol -e -e → Boolean)
  (define (inlinable? x eₓ body)
    (and (not (assignable? x))
         (match eₓ
           [(? -b?) #t]
           [(-x x ℓ)
            (or (symbol? x)
                (equal? (-𝒾-src x) (ℓ-src ℓ)))]
           [_ (and (effect-free? eₓ) (<= (fv-count body x) 1))])))

  (define effect-free? : (-e → Boolean)
    (match-lambda
      [(or (? -v?) (? -x?)) #t]
      [(-begin es) (andmap effect-free? es)]
      [(-begin0 e₀ es) (and (effect-free? e₀) (andmap effect-free? es))]
      [(or (-let-values bnds e _)
           (-letrec-values bnds e _))
       #:when (and bnds e)
       (and (effect-free? e)
            (andmap (compose1 effect-free? Binding-rhs) bnds))]
      [(-set! x e _) #f]
      [(-if e e₁ e₂ _) (and (effect-free? e) (effect-free? e₁) (effect-free? e₂))]
      [(? -rec/c?) #t]
      [(-->i (-var cs c) ds _)
       (define dom-effect-free? (compose1 effect-free? -dom-body))
       (and (andmap dom-effect-free? cs)
            (implies c (dom-effect-free? c))
            (implies ds (andmap dom-effect-free? ds)))]
      [(case--> cases) (andmap effect-free? cases)]
      [_ #f]))
  )
