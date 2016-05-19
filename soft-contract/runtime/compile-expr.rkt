#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         "../utils/main.rkt"
         "../ast/main.rkt"
         "simp.rkt")
(require/typed racket/base
  [hash-empty? ((HashTable -e -e) → Boolean)])

;; Compiled expression ready for substitution
(define-type -⦇e⦈ ((HashTable -e -e) → -e))

(define/memo (⦇⦈ [e : -e]) : -⦇e⦈

  (define-syntax-rule (with-m (m) body ...)
    (λ (m)
      (cond [(hash-ref m e #f) => values]
            [(hash-empty? m) e]
            [else body ...])))

  (match e
    [(-λ xs e*)
     (define ⦇e*⦈ (⦇⦈ e*))
     (define fvs (formals->names xs))
     (with-m (m)
       (-λ xs (⦇e*⦈ (shrink m fvs))))]
    [(-case-λ clauses)
     (define-values (xss fvss ⦇e⦈s)
       (for/lists ([xss  : (Listof (Listof Var-Name))]
                   [fvss : (Listof (℘ Var-Name))]
                   [⦇e⦈s  : (Listof -⦇e⦈)])
                  ([clause clauses])
         (match-define (cons xs eₓ) clause)
         (values xs (list->set xs) (⦇⦈ eₓ))))
     (with-m (m)
       (-case-λ
        (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([xs xss] [fvs fvss] [⦇e⦈ ⦇e⦈s])
          (cons xs (⦇e⦈ (shrink m fvs))))))]
    [(-@ f xs _)
     (define ⦇f⦈ (⦇⦈ f))
     (define ⦇x⦈s (map ⦇⦈ xs))
     (with-m (m)
       (apply -@/simp (⦇f⦈ m) (for/list : (Listof -e) ([⦇x⦈ ⦇x⦈s]) (⦇x⦈ m))))]
    [(-if e₀ e₁ e₂)
     (define ⦇e₀⦈ (⦇⦈ e₀))
     (define ⦇e₁⦈ (⦇⦈ e₁))
     (define ⦇e₂⦈ (⦇⦈ e₂))
     (with-m (m)
       (-if (⦇e₀⦈ m) (⦇e₁⦈ m) (⦇e₂⦈ m)))]
    [(-wcm k v b)
     (define ⦇k⦈ (⦇⦈ k))
     (define ⦇v⦈ (⦇⦈ v))
     (define ⦇b⦈ (⦇⦈ b))
     (with-m (m)
       (-wcm (⦇k⦈ m) (⦇v⦈ m) (⦇b⦈ m)))]
    [(-begin es)
     (define ⦇e⦈s (map ⦇⦈ es))
     (with-m (m)
       (-begin (for/list : (Listof -e) ([⦇e⦈ ⦇e⦈s]) (⦇e⦈ m))))]
    [(-begin0 e₀ es)
     (define ⦇e₀⦈ (⦇⦈ e₀))
     (define ⦇e⦈s (map ⦇⦈ es))
     (with-m (m)
       (-begin0 (⦇e₀⦈ m) (for/list ([⦇e⦈ ⦇e⦈s]) (⦇e⦈ m))))]
    [(-let-values bnds e*)
     (define-values (formals-rev locals ⦇e⦈s-rev)
       (for/fold ([formals-rev : (Listof (Listof Var-Name)) '()]
                  [locals : (℘ Var-Name) ∅]
                  [⦇e⦈s-rev : (Listof -⦇e⦈) '()])
                 ([bnd bnds])
         (match-define (cons xs eₓ) bnd)
         (values (cons xs formals-rev)
                 (set-add-list locals xs)
                 (cons (⦇⦈ eₓ) ⦇e⦈s-rev))))
     (define ⦇e*⦈ (⦇⦈ e*))
     (with-m (m)
       (define bnds*
         (for/fold ([acc : (Listof (Pairof (Listof Var-Name) -e)) '()])
                   ([xs (in-list formals-rev)]
                    [⦇e⦈ (in-list ⦇e⦈s-rev)])
           (cons (cons xs (⦇e⦈ m)) acc)))
       (-let-values bnds* (⦇e*⦈ (shrink m locals))))]
    [(-letrec-values bnds e*)
     (define-values (formals-rev locals ⦇e⦈s-rev)
       (for/fold ([formals-rev : (Listof (Listof Var-Name)) '()]
                  [locals : (℘ Var-Name) ∅]
                  [⦇e⦈s-rev : (Listof -⦇e⦈) '()])
                 ([bnd bnds])
         (match-define (cons xs eₓ) bnd)
         (values (cons xs formals-rev)
                 (set-add-list locals xs)
                 (cons (⦇⦈ eₓ) ⦇e⦈s-rev))))
     (define ⦇e*⦈ (⦇⦈ e*))
     (with-m (m)
       (define m* (shrink m locals))
       (define bnds*
         (for/fold ([acc : (Listof (Pairof (Listof Var-Name) -e)) '()])
                   ([xs (in-list formals-rev)]
                    [⦇e⦈ (in-list ⦇e⦈s-rev)])
           (cons (cons xs (⦇e⦈ m*)) acc)))
       (-letrec-values bnds* (⦇e*⦈ m*)))]
    [(-set! x e*)
     (define ⦇e*⦈ (⦇⦈ e*))
     (with-m (m) (-set! x (⦇e*⦈ m)))]
    [(-amb es)
     (define ⦇e⦈s : (Listof -⦇e⦈) (for/list ([e es]) (⦇⦈ e)))
     (with-m (m)
       (-amb (for/set: : (℘ -e) ([⦇e⦈ ⦇e⦈s]) (⦇e⦈ m))))]
    [(-μ/c z c)
     (define ⦇c⦈ (⦇⦈ c))
     (with-m (m) (-μ/c z (⦇c⦈ m)))]
    [(--> cs d ℓ)
     (define ⦇c⦈s (map ⦇⦈ cs))
     (define ⦇d⦈ (⦇⦈ d))
     (with-m (m)
       (--> (for/list ([⦇c⦈ ⦇c⦈s]) (⦇c⦈ m)) (⦇d⦈ m) ℓ))]
    [(-->i cs mk-d ℓ)
     (define ⦇c⦈s (map ⦇⦈ cs))
     (define ⦇mk-d⦈ (⦇⦈ mk-d))
     (with-m (m)
       (-->i (for/list ([⦇c⦈ ⦇c⦈s]) (⦇c⦈ m)) (assert (⦇mk-d⦈ m) -λ?) ℓ))]
    [(-case-> clauses ℓ)
     (define ⦇clause⦈s : (Listof (Pairof (Listof -⦇e⦈) -⦇e⦈))
       (for/list ([clause clauses])
         (match-define (cons doms rng) clause)
         (cons (map ⦇⦈ doms) (⦇⦈ rng))))
     (with-m (m)
       (-case->
        (for/list : (Listof (Pairof (Listof -e) -e)) ([⦇clause⦈ ⦇clause⦈s])
          (match-define (cons ⦇dom⦈s ⦇rng⦈) ⦇clause⦈)
          (cons (for/list : (Listof -e) ([⦇dom⦈ ⦇dom⦈s]) (⦇dom⦈ m))
                (⦇rng⦈ m)))
        ℓ))]
    [(-struct/c t cs ℓ)
     (define ⦇c⦈s (map ⦇⦈ cs))
     (with-m (m)
       (-struct/c t (for/list ([⦇c⦈ ⦇c⦈s]) (⦇c⦈ m)) ℓ))]
    [_
     (log-debug "⦇⦈: constant ~a" (show-e e))
     (λ (m)
       (cond
         [(hash-ref m e #f) => values]
         [else e]))]))

(: shrink : (HashTable -e -e) (℘ Var-Name) → (HashTable -e -e))
(define (shrink m xs)
  (for/fold ([m* : (HashTable -e -e) m])
            ([eₓ (in-hash-keys m)]
             #:unless (set-empty? (∩ xs (fv eₓ))))
    (hash-remove m* eₓ)))

(: formals->names : -formals → (℘ Var-Name))
(define (formals->names xs)
  (cond
    [(-varargs? xs) (set-add (list->set (-varargs-init xs)) (-varargs-rest xs))]
    [else (list->set xs)]))
