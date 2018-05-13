#lang typed/racket/base

(provide meta-functions@)

(require racket/match
         racket/set
         (only-in racket/function curry)
         racket/list
         racket/bool
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "signatures.rkt")

(define-unit meta-functions@
  (import static-info^ ast-macros^)
  (export meta-functions^)

  (: fv : (U -e (Listof -e)) → (℘ Symbol))
  ;; Compute free variables for expression. Return set of variable names.
  (define (fv e)
    (match e
      [(-x x _) (if (symbol? x) {seteq x} ∅eq)]
      [(-x/c x) {seteq x}]
      [(-λ xs e) (set-remove (fv e) (formals->names xs))]
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
      [(-if e e₁ e₂) (∪ (fv e) (fv e₁) (fv e₂))]
      [(-μ/c _ e) (fv e)]
      [(--> (-var cs c) d _) (∪ (if c (fv c) ∅eq) (fv d) (fv cs))]
      [(-->i cs d)
       (define dom-fv : (-dom → (℘ Symbol))
         (match-lambda
           [(-dom _ ?xs d _) (set-subtract (fv d) (if ?xs (list->seteq ?xs) ∅eq))]))
       (apply ∪ (dom-fv d) (map dom-fv cs))]
      [(-struct/c _ cs _)
       (for/fold ([xs : (℘ Symbol) ∅eq]) ([c cs])
         (∪ xs (fv c)))]
      [(? list? l)
       (for/fold ([xs : (℘ Symbol) ∅eq]) ([e l])
         (∪ xs (fv e)))]
      [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅eq]))

  (: fv-count : -e Symbol → Natural)
  (define (fv-count e z)
    (let go ([e : -e e])
      (match e
        [(-x x _) (if (equal? x z) 1 0)]
        [(-x/c x) (if (equal? x z) 1 0)]
        [(-λ (-var xs x) e)
         (define bound? (or (and x (eq? x z)) (memq z xs)))
         (if bound? 0 (go e))]
        [(-@ f xs _) (apply + (go f) (map go xs))]
        [(-begin es) (apply + (map go es))]
        [(-begin0 e₀ es) (apply + (go e₀) (map go es))]
        [(-let-values bnds e _)
         (define-values (sum₀ bound?)
           (for/fold ([sum : Natural 0] [bound? : Any #f])
                     ([bnd : (Pairof (Listof Symbol) -e) (in-list bnds)])
             (match-define (cons xs eₓ) bnd)
             (values (+ sum (go eₓ)) (or bound? (memq z xs)))))
         (+ sum₀ (if bound? 0 (go e)))]
        [(-letrec-values bnds e _)
         (define bound? (for/or : Any ([bnd (in-list bnds)]) (memq z (car bnd))))
         (if bound?
             0
             (apply + (go e) (map (λ ([bnd : (Pairof Any -e)]) (go (cdr bnd))) bnds)))]
        [(-set! x e) (go e)]
        [(-if e e₁ e₂) (+ (go e) (go e₁) (go e₂))]
        [(-μ/c x e) (if (equal? x z) 0 (go e))]
        [(--> (-var cs c) d _) (+ (go d) (if c (go c) 0) (apply + (map go cs)))]
        [(-->i cs d)
         (define-values (sum _)
           (for/fold ([sum : Natural 0] [bound? : Boolean #f])
                     ([dom (in-list (append cs (list d)))]
                      #:break bound?
                      #:unless bound?)
             (match-define (-dom x _ eₓ _) dom)
             (values (+ sum (go eₓ)) (equal? x z))))
         sum]
        [(-struct/c _ cs _) (apply + (map go cs))]
        [_ 0])))

  (: closed? : -e → Boolean)
  ;; Check whether expression is closed
  (define (closed? e) (set-empty? (fv e)))

  (: free-x/c : -e → (℘ Symbol))
  ;; Return all free references to recursive contracts inside term
  (define (free-x/c e)

    (: go* : (Listof -e) → (℘ Symbol))
    (define (go* xs) (apply ∪ ∅eq (map go xs)))

    (: go/dom : -dom → (℘ Symbol))
    (define go/dom
      (match-lambda
        [(-dom _ ?xs d _) (if ?xs (go (-λ (-var ?xs #f) d)) (go d))]))

    (: go : -e → (℘ Symbol))
    (define (go e)
      (match e
        [(-λ xs e) (go e)]
        [(-@ f xs ctx) (∪ (go f) (go* xs))]
        [(-if i t e) (∪ (go i) (go t) (go e))]
        [(-wcm k v b) (∪ (go k) (go v) (go b))]
        [(-begin0 e es) (∪ (go e) (go* es))]
        [(-let-values bnds e _)
         (apply ∪ (go e) (map (compose1 go Binding-rhs) bnds))]
        [(-letrec-values bnds e _)
         (apply ∪ (go e) (map (compose1 go Binding-rhs) bnds))]
        [(-μ/c _ c) (go c)]
        [(--> (-var cs c) d _) (∪ (go* cs) (if c (go c) ∅eq) (go d))]
        [(-->i cs d) (apply ∪ (go/dom d) (map go/dom cs))]
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


  (define (e/map [m : Subst] [e : -e])

    (: go-list : Subst (Listof -e) → (Listof -e))
    (define (go-list m es)
      (for/list : (Listof -e) ([e es]) (go m e)))

    (: go : Subst -e → -e)
    (define (go m e)
      (with-debugging/off
        ((ans)
         (define go/dom : (-dom → -dom)
           (match-lambda
             [(-dom x ?xs d ℓ)
              (define d* (if ?xs (go (remove-keys m (list->seteq ?xs)) d) (go m d)))
              (-dom x ?xs d* ℓ)]))
         (cond
           [(hash-empty? m) e]
           [else
            (match e
              [(or (-x x _) (-x/c.tmp x))
               #:when x
               (hash-ref m x (λ () e))]
              [(-λ xs e*)
               (-λ xs (go (remove-keys m (formals->names xs)) e*))]
              [(-@ f xs ℓ)
               (-@/simp (go m f) (go-list m xs) ℓ)]
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
                 (for/fold ([bnds*-rev : (Assoc (Listof Symbol) -e) '()]
                            [locals : (℘ Symbol) ∅eq])
                           ([bnd bnds])
                   (match-define (cons xs eₓ) bnd)
                   (values (cons (cons xs (go m eₓ)) bnds*-rev)
                           (set-add* locals xs))))
               (define body* (go (remove-keys m locals) body))
               (-let-values (reverse bnds*-rev) body* ℓ)]
              [(-letrec-values bnds body ℓ)
               (define locals
                 (for/fold ([locals : (℘ Symbol) ∅eq])
                           ([bnd bnds])
                   (match-define (cons xs _) bnd)
                   (set-add* locals xs)))
               (define m* (remove-keys m locals))
               (define bnds* : (Assoc (Listof Symbol) -e)
                 (for/list ([bnd bnds])
                   (match-define (cons xs eₓ) bnd)
                   (cons xs (go m* eₓ))))
               (define body* (go m* body))
               (-letrec-values bnds* body* ℓ)]
              [(-set! x e*)
               (assert (not (hash-has-key? m x)))
               (-set! x (go m e*))]
              [(-μ/c z c)
               (-μ/c z (go (remove-keys m {seteq z}) c))]
              [(--> (-var cs c) d ℓ)
               (--> (-var (go-list m cs) (and c (go m c))) (go m d) ℓ)]
              [(-->i cs d)
               (-->i (map go/dom cs) (go/dom d))]
              [(-struct/c t cs ℓ)
               (-struct/c t (go-list m cs) ℓ)]
              [_
               ;(printf "unchanged: ~a @ ~a~n" (show-e e) (show-subst m))
               e])]))
        (printf "go: ~a ~a -> ~a~n" (show-subst m) (show-e e) (show-e ans))))

    (go m e))

  (: e/ : Symbol -e -e → -e)
  (define (e/ x eₓ e) (e/map (hasheq x eₓ) e))

  (: remove-keys : Subst (℘ Symbol) → Subst)
  (define (remove-keys m xs)
    (for/fold ([m : Subst m]) ([x (in-set xs)])
      (hash-remove m x)))

  (: formals->names : -formals → (℘ Symbol))
  (define (formals->names xs) (-var->set xs #:eq? #t))

  (: first-forward-ref : (Listof -dom) → (Option Symbol))
  (define (first-forward-ref doms)
    (define-set seen : Symbol #:eq? #t #:as-mutable-hash? #t)
    (for/or : (Option Symbol) ([dom (in-list doms)])
      (match-define (-dom x ?xs _ _) dom)
      (seen-add! x)
      (and ?xs
           (for/or : (Option Symbol) ([x (in-list ?xs)] #:unless (seen-has? x))
             x))))
  )
