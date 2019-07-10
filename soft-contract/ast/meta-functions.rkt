#lang typed/racket/base

(provide meta-functions@)

(require racket/match
         racket/set
         racket/string
         (only-in racket/function curry)
         racket/list
         racket/bool
         typed/racket/unit
         set-extras
         unreachable
         "../utils/main.rkt"
         "signatures.rkt")

(define-unit meta-functions@
  (import static-info^ ast-macros^)
  (export meta-functions^)

  (: fv : -e → (℘ Symbol))
  ;; Compute free variables for expression. Return set of variable names.
  (define (fv e)
    (match e
      [(-x x _) (if (symbol? x) {seteq x} ∅eq)]
      [(-λ xs e _) (set-subtract (fv e) (formals->names xs))]
      [(-case-λ cases _) (apply ∪ ∅eq (map fv cases))]
      [(-@ f xs _) (apply ∪ (fv f) (map fv xs))]
      [(-begin es) (apply ∪ ∅eq (map fv es))]
      [(-begin0 e₀ es) (apply ∪ (fv e₀) (map fv es))]
      [(-let-values bnds e _)
       (define-values (bound rhs:fv)
         (for/fold ([bound : (℘ Symbol) ∅eq] [rhs:fv : (℘ Symbol) ∅eq])
                   ([bnd bnds])
           (match-define (cons xs rhs) bnd)
           (values (set-add* bound xs) (∪ rhs:fv (fv rhs)))))
       (∪ rhs:fv (set-subtract (fv e) bound))]
      [(-letrec-values bnds e _)
       (define bound (for/fold ([bound : (℘ Symbol) ∅eq]) ([bnd bnds])
                       (set-add* bound (car bnd))))
       (set-subtract (apply ∪ (fv e) (map (compose1 fv (inst cdr Any -e)) bnds)) bound)]
      [(-set! x e _) (if (symbol? x) (set-add (fv e) x) (fv e))]
      [(-if e e₁ e₂ _) (∪ (fv e) (fv e₁) (fv e₂))]
      [(-rec/c (-x x _)) (if (symbol? x) {set x} ∅eq)]
      [(-->i (-var cs c) d _)
       (define dom-fv : (-dom → (℘ Symbol))
         (match-lambda
           [(-dom _ ?xs d _) (set-subtract (fv d) (if ?xs (list->seteq ?xs) ∅eq))]))
       (∪ (apply ∪ (if c (dom-fv c) ∅eq) (map dom-fv cs))
          (if d (apply ∪ ∅eq (map dom-fv d)) ∅eq))]
      [(case--> cases) (apply ∪ ∅eq (map fv cases))]
      [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅eq]))

  (: fv-count : -e Symbol → Natural)
  (define (fv-count e z)
    (let go ([e : -e e])
      (match e
        [(-x x _) (if (equal? x z) 1 0)]
        [(-λ (-var xs x) e _)
         (define bound? (or (and x (eq? x z)) (memq z xs)))
         (if bound? 0 (go e))]
        [(-case-λ cases _) (apply + (map go cases))]
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
        [(-set! x e _) (go e)]
        [(-if e e₁ e₂ _) (+ (go e) (go e₁) (go e₂))]
        [(-rec/c (-x x _)) (if (equal? x z) 1 0)]
        [(-->i (-var cs c) d _)
         (define dom-count : (-dom → Natural)
           (match-lambda [(-dom x _ eₓ _) (if (equal? x z) 0 (go eₓ))]))
         (+ (apply + (if c (dom-count c) 0) (map dom-count cs))
            (if d (apply + (map dom-count d)) 0))]
        [(case--> cases) (apply + (map go cases))]
        [_ 0])))

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

    (: go--->i : Subst -->i → -->i)
    (define (go--->i m c)
      (define go/dom : (-dom → -dom)
        (match-lambda
          [(-dom x ?xs d ℓ)
           (define d* (if ?xs (go (remove-keys m (list->seteq ?xs)) d) (go m d)))
           (-dom x ?xs d* ℓ)]))
      (match-define (-->i cs d t?) c)
      (-->i (var-map go/dom cs) (and d (map go/dom d)) t?))

    (: go : Subst -e → -e)
    (define (go m e)
      (with-debugging/off
        ((ans)
         
         (cond
           [(hash-empty? m) e]
           [else
            (match e
              [(-x x _) (hash-ref m x (λ () e))]
              [(-λ xs e* ℓ)
               (-λ xs (go (remove-keys m (formals->names xs)) e*) ℓ)]
              [(-case-λ cases ℓ)
               (-case-λ (cast (go-list m cases) (Listof -λ)) ℓ)]
              [(-@ f xs ℓ)
               (-@/simp (go m f) (go-list m xs) ℓ)]
              [(-if e₀ e₁ e₂ ℓ)
               (-if (go m e₀) (go m e₁) (go m e₂) ℓ)]
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
              [(-set! x e* ℓ)
               (assert (not (hash-has-key? m x)))
               (-set! x (go m e*) ℓ)]
              [(-rec/c (-x x _)) (if (hash-has-key? m x) !!! e)]
              [(? -->i? c) (go--->i m c)]
              [(case--> cases) (case--> (map (curry go--->i m) cases))]
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

  (: formals->names ([-formals] [#:eq? Boolean] . ->* . (℘ Symbol)))
  (define (formals->names xs #:eq? [use-eq? #t]) (var->set xs #:eq? use-eq?))

  (: first-forward-ref : (Listof -dom) → (Option Symbol))
  (define (first-forward-ref doms)
    (define-set seen : Symbol #:eq? #t #:mutable? #t)
    (for/or : (Option Symbol) ([dom (in-list doms)])
      (match-define (-dom x ?xs _ _) dom)
      (seen-add! x)
      (and ?xs
           (for/or : (Option Symbol) ([x (in-list ?xs)] #:unless (seen-has? x))
             x)))) 

  (: +x! : (U Symbol Integer) * → Symbol)
  (define (+x! . prefixes)
    (define (stuff->string x) (format "~a" x))
    (define prefix (string-join (map stuff->string prefixes) "_" #:after-last "_"))
    (gensym prefix))

  (: +x!/memo : (U Symbol Integer) * → Symbol)
  (define +x!/memo
    (let ([m : (HashTable (Listof (U Symbol Integer)) Symbol) (make-hash)])
      (λ [xs : (U Symbol Integer) *]
        (hash-ref! m xs (λ () (apply +x! xs))))))

  (define (any/c? x) (equal? x 'any/c))
  
  )
