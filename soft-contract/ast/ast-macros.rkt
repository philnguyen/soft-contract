#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/splicing
         racket/set
         typed/racket/unit
         "signatures.rkt")

(define-unit ast-macros@
  (import meta-functions^ static-info^)
  (export ast-macros^)

  (: -define : Symbol -e → -define-values)
  (define (-define x e) (-define-values (list x) e))

  (: -cond : (Listof (Pairof -e -e)) -e → -e)
  (define (-cond cases default)
    (foldr (λ ([alt : (Pairof -e -e)] [els : -e])
             (match-define (cons cnd thn) alt)
             (-if cnd thn els))
           default
           cases))

  ;; Make conjunctive and disjunctive contracts
  (splicing-local
      ((: -app/c : Symbol → (Listof (Pairof ℓ -e)) → -e)
       (define ((-app/c o) args)
         (let go ([args : (Listof (Pairof ℓ -e)) args])
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

  (: -list/c : (Listof (Pairof ℓ -e)) → -e)
  (define (-list/c args)
    (foldr (λ ([arg : (Pairof ℓ -e)] [acc : -e])
             (match-define (cons ℓ e) arg)
             (-cons/c e acc ℓ))
           'null?
           args))

  (: -list : (Listof (Pairof ℓ -e)) → -e)
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
       (for/list : (Listof (Pairof (Listof Symbol) -e)) ([x (in-list xs)]
                                                         [e (in-list es)])
         (cons (list x) e))
       e
       ℓ)]
     [(f xs ℓ) (-@ f xs ℓ)]))

  (: -let-values/simp : (Listof (Pairof (Listof Symbol) -e)) -e ℓ → -e)
  (define -let-values/simp
    (match-lambda**
     [('() e _) e]
     [((list (cons (list x) eₓ)) (-x x _) _) eₓ]
     [((and bindings (list (cons (list lhss) rhss) ...)) body ℓ)
      (define-values (bindings-rev inlines)
        (for/fold ([bindings-rev : (Listof (Pairof (Listof Symbol) -e)) '()]
                   [inlines : Subst (hasheq)])
                  ([lhs (in-list lhss)]
                   [rhs (in-list rhss)]
                   #:when (and (symbol? lhs) (-e? rhs)))
          (if (inlinable? lhs rhs)
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

  (: inlinable? : Symbol -e → Boolean)
  (define (inlinable? x e)
    (and (not (assignable? x))
         (match e
           [(? -b?) #t]
           [(-x x ℓ)
            (or (symbol? x)
                (equal? (-𝒾-src x) (ℓ-src ℓ)))]
           [_ #f])))
  )
