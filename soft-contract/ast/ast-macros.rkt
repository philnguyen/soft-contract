#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/splicing
         racket/set
         typed/racket/unit
         "../utils/list.rkt"
         "signatures.rkt")

(define-unit ast-macros@
  (import meta-functions^ static-info^)
  (export ast-macros^)

  (: -define : Symbol -e → -define-values)
  (define (-define x e) (-define-values (list x) e))

  (: -cond : (Assoc -e -e) -e → -e)
  (define (-cond cases default)
    (foldr (λ ([alt : (Pairof -e -e)] [els : -e])
             (match-define (cons cnd thn) alt)
             (-if cnd thn els))
           default
           cases))

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
    (-struct/c -𝒾-cons (list c d) ℓ))

  (: -box/c : -e ℓ → -e)
  (define (-box/c c ℓ)
    (-struct/c -𝒾-box (list c) ℓ))

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

  (: -and : -e * → -e)
  ;; Return ast representing conjuction of 2 expressions
  (define -and
    (match-lambda*
      [(list) -tt]
      [(list e) e]
      [(cons e es) (-if e (apply -and es) -ff)]))

  (: -comp/c : Symbol -e ℓ → -e)
  ;; Return ast representing `(op _ e)`
  (define (-comp/c op e ℓ)
    (define x (+x! 'cmp))
    (define 𝐱 (-x x (ℓ-with-id ℓ 'cmp)))
    (match-define (list ℓ₀ ℓ₁) (ℓ-with-ids ℓ 2))
    (-λ (list x)
        (-and (-@ 'real? (list 𝐱) ℓ₀)
              (-@ op (list 𝐱 e) ℓ₁))))

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
     [((-λ (? list? xs) e) es ℓ)
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

  (: -if/simp : -e -e -e → -e)
  (define -if/simp
    (match-lambda**
     [((-b #f) _ e) e]
     [((-b _ ) e _) e]
     [(i t e) (-if i t e)]))

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
      [(-@ (and (? -o?) (not (? -st-mut?))) xs _) (andmap effect-free? xs)]
      [(-begin es) (andmap effect-free? es)]
      [(-begin0 e₀ es) (and (effect-free? e₀) (andmap effect-free? es))]
      [(or (-let-values bnds e _)
           (-letrec-values bnds e _))
       #:when (and bnds e)
       (and (effect-free? e)
            (andmap (compose1 effect-free? (inst cdr Any -e)) bnds))]
      [(-set! x e) #f]
      [(-if e e₁ e₂) (and (effect-free? e) (effect-free? e₁) (effect-free? e₂))]
      [(-μ/c _ e) (effect-free? e)]
      [(--> cs d _)
       (and (effect-free? d)
            (match cs
              [(-var cs c) (and (effect-free? c) (andmap effect-free? cs))]
              [(? list? cs) (andmap effect-free? cs)]))]
      [(-->i cs d) (andmap (compose1 effect-free? -dom-body) (cons d cs))]
      [(-struct/c _ cs _) (andmap effect-free? cs)]
      [_ #f]))
  )
