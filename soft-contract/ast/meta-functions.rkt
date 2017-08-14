#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         (only-in racket/function curry)
         racket/list
         racket/bool
         set-extras
         "../utils/main.rkt"
         "definition.rkt"
         "shorthands.rkt")

(: fv : (U -e (Listof -e)) → (℘ Symbol))
;; Compute free variables for expression. Return set of variable names.
(define (fv e)
  (match e
    [(-x x _) {seteq x}]
    [(-λ xs e)
     (define bound
       (match xs
         [(-var zs z) (set-add (list->seteq zs) z)]
         [(? list? xs) (list->seteq xs)]))
     (set-remove (fv e) bound)]
    [(-@ f xs _)
     (for/fold ([FVs (fv f)]) ([x xs]) (∪ FVs (fv x)))]
    [(-begin es) (fv es)]
    [(-begin0 e₀ es) (∪ (fv e₀) (fv es))]
    [(-let-values bnds e _)
     (define-values (bound FV_rhs)
       (for/fold ([bound : (℘ Symbol) ∅eq] [FV_rhs : (℘ Symbol) ∅eq]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add* bound xs) (∪ FV_rhs (fv rhs)))))
     (∪ FV_rhs (set-remove (fv e) bound))]
    [(-letrec-values bnds e _)
     (define bound
       (for/fold ([bound : (℘ Symbol) ∅eq]) ([bnd bnds])
         (set-add* bound (car bnd))))
     
     (for/fold ([xs : (℘ Symbol) (set-remove (fv e) bound)]) ([bnd bnds])
       (set-remove (fv (cdr bnd)) bound))]
    [(-set! x e)
     (match x
       [(? symbol? x) (set-add (fv e) x)]
       [_ (fv e)])]
    #;[(.apply f xs _) (set-union (fv f d) (fv xs d))]
    [(-if e e₁ e₂) (∪ (fv e) (fv e₁) (fv e₂))]
    [(-μ/c _ e) (fv e)]
    [(--> cs d _)
     (match cs
       [(-var cs c) (∪ (fv c) (fv d) (fv cs))]
       [(? list? cs) (∪ (fv d) (fv cs))])]
    [(-->i cs mk-d _) (apply ∪ (fv mk-d) (map fv cs))]
    [(-case-> clauses _)
     (for/unioneq : (℘ Symbol) ([clause clauses])
       (match-define (cons cs d) clause)
       (apply ∪ (fv d) (map fv cs)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (℘ Symbol) ∅eq]) ([c cs])
       (∪ xs (fv c)))]
    [(? list? l)
     (for/fold ([xs : (℘ Symbol) ∅eq]) ([e l])
       (∪ xs (fv e)))]
    [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅eq]))

(: bv : (U -e (Listof -e)) → (℘ Symbol))
(define (bv e)
  (match e
    [(-x x _) ∅eq]
    [(-λ xs e)
     (define bound
       (match xs
         [(-var zs z) (set-add (list->seteq zs) z)]
         [(? list? xs) (list->seteq xs)]))
     (∪ (bv e) bound)]
    [(-@ f xs _) (∪ (bv f) (bv xs))]
    [(-begin es) (bv es)]
    [(-begin0 e₀ es) (∪ (bv e₀) (bv es))]
    [(-let-values bnds e _)
     (∪ (for/unioneq : (℘ Symbol) ([bnd (in-list bnds)])
                     (match-define (cons xs rhs) bnd)
                     (∪ (list->seteq xs) (bv rhs)))
        (bv e))]
    [(-letrec-values bnds e _)
     (∪ (for/unioneq : (℘ Symbol) ([bnd (in-list bnds)])
                     (match-define (cons xs rhs) bnd)
                     (∪ (list->seteq xs) (bv rhs)))
        (bv e))]
    [(-set! x e) (bv e)]
    #;[(.apply f xs _) (set-union (fv f d) (fv xs d))]
    [(-if e e₁ e₂) (∪ (bv e) (bv e₁) (bv e₂))]
    [(-μ/c _ e) (bv e)]
    [(--> cs d _)
     (match cs
       [(-var cs c) (∪ (bv c) (bv d) (bv cs))]
       [(? list? cs) (∪ (bv d) (bv cs))])]
    [(-->i cs mk-d _) (apply ∪ (bv mk-d) (map bv cs))]
    [(-case-> clauses _)
     (for/unioneq : (℘ Symbol) ([clause clauses])
       (match-define (cons cs d) clause)
       (apply ∪ (bv d) (map bv cs)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (℘ Symbol) ∅eq]) ([c cs])
       (∪ xs (bv c)))]
    [(? list? l)
     (for/fold ([xs : (℘ Symbol) ∅eq]) ([e l])
       (∪ xs (bv e)))]
    [_ (log-debug "BV⟦~a⟧ = ∅~n" e) ∅eq]))

(: closed? : -e → Boolean)
;; Check whether expression is closed
(define (closed? e) (set-empty? (fv e)))

(: free-x/c : -e → (℘ Symbol))
;; Return all free references to recursive contracts inside term
(define (free-x/c e)

  (: go* : (Listof -e) → (℘ Symbol))
  (define (go* xs) (for/unioneq : (℘ Symbol) ([x xs]) (go x)))

  (: go : -e → (℘ Symbol))
  (define (go e)
    (match e
      [(-λ xs e) (go e)]
      [(-case-λ body)
       (for/unioneq : (℘ Symbol) ([p body]) (go (cdr p)))]
      [(-@ f xs ctx) (∪ (go f) (go* xs))]
      [(-if i t e) (∪ (go i) (go t) (go e))]
      [(-wcm k v b) (∪ (go k) (go v) (go b))]
      [(-begin0 e es) (∪ (go e) (go* es))]
      [(-let-values bnds e _)
       (∪ (for/unioneq : (℘ Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-letrec-values bnds e _)
       (∪ (for/unioneq : (℘ Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-μ/c _ c) (go c)]
      [(--> cs d _)
       (match cs
         [(-var cs c) (∪ (go* cs) (go c) (go d))]
         [(? list? cs) (∪ (go* cs) (go d))])]
      [(-->i cs mk-d _) (∪ (go* cs) (go mk-d))]
      [(-case-> clauses _)
       (for/unioneq : (℘ Symbol) ([clause clauses])
         (match-define (cons cs d) clause)
         (∪ (go d) (go* cs)))]
      [(-struct/c t cs _) (go* cs)]
      [(-x/c.tmp x) (seteq x)]
      [_ ∅eq]))
  
  (go e))

#;(: find-calls : -e (U -𝒾 -•) → (℘ (Listof -e)))
;; Search for all invocations of `f-id` in `e`
#;(define (find-calls e f-id)
  (define-set calls : (Listof -e))
  (let go! : Void ([e e])
    (match e
      [(-@ f xs _)
       (go! f)
       (for-each go! xs)
       (when (equal? f f-id)
         (calls-add! xs))]
      [_ (void)]))
  calls)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Substitution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Subst (HashTable -e -e))

(define m∅ : Subst (hash))

(define (e/map [m : Subst] [e : -e])

  (: go-list : Subst (Listof -e) → (Listof -e))
  (define (go-list m es)
    (with-debugging/off
      ((ans) (for/list : (Listof -e) ([e es]) (go m e)))
      (printf "go-list: ~a ~a -> ~a~n" (show-subst m) (map show-e es) (map show-e ans))))

  (: go : Subst -e → -e)
  (define (go m e)
    (with-debugging/off
      ((ans)
       (cond
         [(hash-empty? m) e]
         [(hash-ref m e #f) => values]
         [else
          (match e
            [(-λ xs e*)
             (-λ xs (go (shrink m (formals->names xs)) e*))]
            [(-case-λ clauses)
             (define clauses*
               (for/list : (Listof (Pairof (Listof Symbol) -e)) ([clause clauses])
                 (match-define (cons xs eₓ) clause)
                 (cons xs (go (shrink m (formals->names xs)) eₓ))))
             (-case-λ clauses*)]
            [(-@ f xs ℓ)
             (-@ (go m f) (go-list m xs) ℓ)]
            [(-if e₀ e₁ e₂)
             (-if (go m e₀) (go m e₁) (go m e₂))]
            [(-wcm k v b)
             (-wcm (go m k) (go m v) (go m b))]
            [(-begin es)
             (-begin (go-list m es))]
            [(-begin0 e₀ es)
             (-begin0 (go m e₀) (go-list m es))]
            [(-let-values bnds body ℓ)
             (define-values (bnds*-rev locals)
               (for/fold ([bnds*-rev : (Listof (Pairof (Listof Symbol) -e)) '()]
                          [locals : (℘ Symbol) ∅eq])
                         ([bnd bnds])
                 (match-define (cons xs eₓ) bnd)
                 (values (cons (cons xs (go m eₓ)) bnds*-rev)
                         (set-add* locals xs))))
             (define body* (go (shrink m locals) body))
             (-let-values (reverse bnds*-rev) body* ℓ)]
            [(-letrec-values bnds body ℓ)
             (define locals
               (for/fold ([locals : (℘ Symbol) ∅eq])
                         ([bnd bnds])
                 (match-define (cons xs _) bnd)
                 (set-add* locals xs)))
             (define m* (shrink m locals))
             (define bnds* : (Listof (Pairof (Listof Symbol) -e))
               (for/list ([bnd bnds])
                 (match-define (cons xs eₓ) bnd)
                 (cons xs (go m* eₓ))))
             (define body* (go m* body))
             (-letrec-values bnds* body* ℓ)]
            [(-set! x e*)
             (-set! x (go m e*))]
            [(-μ/c z c)
             (-μ/c z (go (shrink m {seteq z}) c))]
            [(--> cs d ℓ)
             (match cs
               [(-var cs c) (--> (-var (go-list m cs) (go m c)) (go m d) ℓ)]
               [(? list? cs) (--> (go-list m cs) (go m d) ℓ)])]
            [(-->i cs mk-d ℓ)
             (-->i (go-list m cs) (assert (go m mk-d) -λ?) ℓ)]
            [(-case-> clauses ℓ)
             (define clauses*
               (for/list : (Listof (Pairof (Listof -e) -e)) ([clause clauses])
                 (match-define (cons cs d) clause)
                 (cons (go-list m cs) (go m d))))
             (-case-> clauses* ℓ)]
            [(-struct/c t cs ℓ)
             (-struct/c t (go-list m cs) ℓ)]
            [_
             ;(printf "unchanged: ~a @ ~a~n" (show-e e) (show-subst m))
             e])]))
      (printf "go: ~a ~a -> ~a~n" (show-subst m) (show-e e) (show-e ans))))

  (go m e))

(: e/ : (U -x -x/c.tmp) -e -e → -e)
;; Substitution, where `x` can be an (open) term rather than just a free variable.
(define (e/ x eₓ e) (e/map ((inst hash -e -e) x eₓ) e))

(: shrink : Subst (℘ Symbol) → Subst)
(define (shrink m xs)
  (for/fold ([m* : Subst m])
            ([eₓ (in-hash-keys m)]
             #:unless (set-empty? (∩ xs (fv eₓ))))
    (hash-remove m* eₓ)))

(: formals->names : -formals → (℘ Symbol))
(define (formals->names xs)
  (cond
    [(-var? xs) (set-add (list->seteq (-var-init xs)) (-var-rest xs))]
    [else (list->seteq xs)]))

(define (show-subst [m : Subst]) : (Listof Sexp)
  (for/list ([(k v) m]) `(,(show-e k) ↦ ,(show-e v))))

(: -@/opt : -e (Listof -e) ℓ → -e)
(define -@/opt
  (match-lambda**
   [('values (list x) _) x]
   [('not (list (-b b)) _) (-b (not b))]
   [('apply (cons (and fun (or (? -λ?) (? -o?))) args) ℓ)
    (-@/opt fun args ℓ)]
   [((-λ (? list? xs) e) es ℓ)
    #:when (= (length xs) (length es))
    (-let-values/opt
     (for/list : (Listof (Pairof (Listof Symbol) -e)) ([x (in-list xs)]
                                                       [e (in-list es)])
       (cons (list x) e))
     e
     ℓ)]
   [(f xs ℓ) (-@ f xs ℓ)]))

(: -let-values/opt : (Listof (Pairof (Listof Symbol) -e)) -e ℓ → -e)
(define -let-values/opt
  (match-lambda**
   [((list (cons x eₓ)) (-x x _) _) eₓ]
   [(bindings body ℓ) (printf "lvo: ~a~n" (show-e body)) (-let-values bindings body ℓ)]))

(: -if/opt : -e -e -e → -e)
(define -if/opt
  (match-lambda**
   [((-b #f) _ e) e]
   [((-b _ ) e _) e]
   [(i t e) (-if i t e)]))
