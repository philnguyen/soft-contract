#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/function
         racket/list
         "../utils/main.rkt"
         "../utils/untyped-macros.rkt"
         "definition.rkt")

(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)])

(: fv : (U -e (Listof -e)) → (℘ Var-Name))
;; Compute free variables for expression. Return set of variable names.
(define (fv e)
  (match e
    [(-x x) {seteq x}]
    [(-λ xs e)
     (define bound
       (match xs
         [(-varargs zs z) (set-add (list->seteq zs) z)]
         [(? list? xs) (list->seteq xs)]))
     (-- (fv e) bound)]
    [(-@ f xs _)
     (for/fold ([FVs (fv f)]) ([x xs]) (∪ FVs (fv x)))]
    [(-begin es) (fv es)]
    [(-begin0 e₀ es) (∪ (fv e₀) (fv es))]
    [(-let-values bnds e)
     (define-values (bound FV_rhs)
       (for/fold ([bound : (℘ Var-Name) ∅eq] [FV_rhs : (℘ Var-Name) ∅eq]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ FV_rhs (fv rhs)))))
     (∪ FV_rhs (-- (fv e) bound))]
    [(-letrec-values bnds e)
     (define bound
       (for/fold ([bound : (℘ Var-Name) ∅eq]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     
     (for/fold ([xs : (℘ Var-Name) (-- (fv e) bound)]) ([bnd bnds])
       (-- (fv (cdr bnd)) bound))]
    [(-set! x e) (set-add (fv e) x)]
    #;[(.apply f xs _) (set-union (fv f d) (fv xs d))]
    [(-if e e₁ e₂) (∪ (fv e) (fv e₁) (fv e₂))]
    [(-amb es)
     (for/fold ([xs : (℘ Var-Name) ∅eq]) ([e es])
       (∪ xs (fv e)))]
    [(-μ/c _ e) (fv e)]
    [(--> cs d _) (apply ∪ (fv d) (map fv cs))]
    [(-->i cs mk-d _) (apply ∪ (fv mk-d) (map fv cs))]
    [(-case-> clauses _)
     (for/unioneq : (℘ Var-Name) ([clause clauses])
       (match-define (cons cs d) clause)
       (apply ∪ (fv d) (map fv cs)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (℘ Var-Name) ∅eq]) ([c cs])
       (∪ xs (fv c)))]
    [(? list? l)
     (for/fold ([xs : (℘ Var-Name) ∅eq]) ([e l])
       (∪ xs (fv e)))]
    [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅eq]))

(module+ test
  (require typed/rackunit)
  
  (check-equal? (fv -tt) ∅)
  (check-equal? (fv (-λ '(x) (-x 'x))) ∅)
  (check-equal? (fv (-x 'x)) {set 'x})
  (check-equal? (fv (-𝒾 'cons 'Λ)) ∅)
  (check-equal? (fv (-λ '(x) (-λ '(y) (-@ (-x 'f) (list (-x 'y) (-x 'x)) +ℓ₀)))) {set 'f}))

(: closed? : -e → Boolean)
;; Check whether expression is closed
(define (closed? e) (set-empty? (fv e)))

(: checks# : (Rec X (U -top-level-form
                       -e
                       -general-top-level-form
                       -e
                       -module
                       -begin/top
                       -module-level-form
                       (Listof X))) → Integer)
;; Statically count number of unsafe operations needing checks
(define checks#
  (match-lambda
   [(? list? es) (for/sum : Integer ([e (in-list es)]) (checks# e))]
   [(-define-values _ e) (checks# e)]
   [(-λ _ e) (checks# e)]
   [(-@ f xs _) (+ 1 (checks# f) (checks# xs))]
   [(-if i t e) (+ (checks# i) (checks# t) (checks# e))]
   [(-wcm k v e) (+ (checks# k) (checks# v) (checks# e))]
   [(-begin0 e es) (+ (checks# e) (checks# es))]
   [(-let-values bindings e)
    (+ (for/sum : Integer ([binding (in-list bindings)])
         (match-define (cons _ eₓ) binding)
         (checks# eₓ))
       (checks# e))]
   [(-letrec-values bindings e)
    (+ (for/sum : Integer ([binding (in-list bindings)])
         (match-define (cons _ eₓ) binding)
         (checks# eₓ))
       (checks# e))]
   [(-amb es) (for/sum ([e (in-set es)]) (checks# e))]
   [(-μ/c _ c) (checks# c)]
   [(--> cs d _) (+ (checks# cs) (checks# d))]
   [(-->i cs mk-d _) (+ (checks# cs) (checks# mk-d))]
   [(-case-> clauses _)
    (for/sum : Integer ([clause clauses])
      (match-define (cons cs d) clause)
      (+ (checks# cs) (checks# d)))]
   [(-struct/c _ cs _) (checks# cs)]

   [(-module _ body) (checks# body)]
   ;; FIXME count up for primitives
   [_ 0]))

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
      [(-let-values bnds e)
       (∪ (for/unioneq : (℘ Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-letrec-values bnds e)
       (∪ (for/unioneq : (℘ Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-amb es) (for/unioneq : (℘ Symbol) ([e es]) (go e))]
      [(-μ/c _ c) (go c)]
      [(--> cs d _) (∪ (go* cs) (go d))]
      [(-->i cs mk-d _) (∪ (go* cs) (go mk-d))]
      [(-case-> clauses _)
       (for/unioneq : (℘ Symbol) ([clause clauses])
         (match-define (cons cs d) clause)
         (∪ (go d) (go* cs)))]
      [(-struct/c t cs _) (go* cs)]
      [(-x/c.tmp x) (seteq x)]
      [_ ∅eq]))
  
  (go e))

(: unroll : Integer -e -e → -e)
;; Unroll reference to recursive contract
(define (unroll x c e)
  (let go ([e : -e e])

    (: go-bnd (∀ (X) (Pairof X -e) → (Pairof X -e)))
    (define (go-bnd bnd)
      (match-define (cons xs e) bnd)
      (cons xs (go e)))

    (match e
      [(-λ xs e*) (-λ xs (go e*))]
      [(-case-λ clauses) (-case-λ (map (inst go-bnd (Listof Var-Name)) clauses))]
      [(-@ f xs l) (-@ (go f) (map go xs) l)]
      [(-if e₀ e₁ e₂) (-if (go e₀) (go e₁) (go e₂))]
      [(-wcm k v b) (-wcm (go k) (go v) (go b))]
      [(-begin0 e₀ es) (-begin0 (go e₀) (map go es))]
      [(-let-values bnds e*)
       (-let-values (map (inst go-bnd (Listof Var-Name)) bnds) (go e*))]
      [(-letrec-values bnds e*)
       (-letrec-values (map (inst go-bnd (Listof Var-Name)) bnds) (go e*))]
      [(-set! z e*) (-set! z (go e*))]
      [(-amb es) (-amb (map/set go es))]
      [(-μ/c z e*) (if (= z x) e (-μ/c z (go e*)))]
      [(--> cs d ℓ) (--> (map go cs) (go d) ℓ)]
      [(-->i cs mk-d ℓ)
       (-->i (map go cs) (assert (go mk-d) -λ?) ℓ)]
      [(-case-> clauses ℓ)
       (define clauses* : (Listof (Pairof (Listof -e) -e))
         (for/list ([clause clauses])
           (match-define (cons cs d) clause)
           (cons (map go cs) (go d))))
       (-case-> clauses* ℓ)]
      [(-struct/c si cs ℓ) (-struct/c si (map go cs) ℓ)]
      [(-x/c z) (if (= z x) c e)]
      [_
       (log-debug "unroll: ignore ~a" (show-e e))
       e])))

(: find-calls : -e (U -𝒾 -•) → (℘ (Listof -e)))
;; Search for all invocations of `f-id` in `e`
(define (find-calls e f-id)
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

(: prim-name->unsafe-prim : Symbol → -o)
;; Convert primitive name to (unsafe) primitive
(define prim-name->unsafe-prim
  (let ([specials : (HashTable Symbol -o) (make-hasheq)]
        [aliases : (HashTable Symbol Symbol) (make-hasheq)]
        [mk-struct-info : (Any → -struct-info)
         (match-lambda
           [`(,(? symbol? t) ,(? boolean? bs) ...)
            (-struct-info
             (-𝒾 t 'Λ)
             (length bs)
             (for/set: : (℘ Natural) ([b bs] [i : Natural (in-naturals)] #:when b)
               i))])])
    (for ([dec prims])
      (match dec
        [`(#:alias ,(? symbol? x) ,(? symbol? y))
         (hash-set! aliases x y)]
        [`(#:struct-cons ,(? symbol? x) ,si)
         (hash-set! specials x (-st-mk (mk-struct-info si)))]
        [`(#:struct-pred ,(? symbol? x) ,si)
         (hash-set! specials x (-st-p (mk-struct-info si)))]
        [`(#:struct-acc ,(? symbol? x) ,si ,(? exact-nonnegative-integer? i))
         (hash-set! specials x (-st-ac (mk-struct-info si) i))]
        [`(#:struct-acc ,(? symbol? x) ,si ,(? exact-nonnegative-integer? i))
         (hash-set! specials x (-st-mut (mk-struct-info si) i))]
        [_ (void)]))
    (λ (x)
      (cond
        [(hash-ref specials x #f)]
        [(hash-ref aliases x #f) => prim-name->unsafe-prim]
        [else x]))))

(: α-rename : (case->
               [-e → -e]
               [-module → -module]))
;; Make sure each binding has a unique name
(define (α-rename e)
  (define-type S->S (HashTable Symbol Symbol))
  ;; Map each bound name to its ith appearance. `0` means first, no need to rename
  (define ith : (HashTable Symbol Natural) (make-hasheq))

  (: new-binder! : S->S Var-Name → (Values S->S Var-Name))
  ;; Updates the global table to remember how many times `x` has been seen,
  ;; and updates the local environment that renames free occurences of `x`
  (define (new-binder! names x)
    (cond
      [(integer? x) (values names x)]
      [else
       (cond
         [(hash-ref ith x #f) =>
          (λ (i) (hash-set! ith x (+ 1 i)))]
         [else (hash-set! ith x 0)])
       (define x*
         (match (hash-ref ith x)
           [0 x]
           [i (format-symbol "~a~a" x (n-sub i))]))
       (values (hash-set names x x*) x*)]))

  (: new-binders! : S->S (Listof Var-Name) → (Values S->S (Listof Var-Name)))
  (define (new-binders! m xs)
    (define-values (m* xs*-rev)
      (for/fold ([m : S->S m] [xs-rev : (Listof Var-Name) '()])
                ([x xs])
        (define-values (m* x*) (new-binder! m x))
        (values m* (cons x* xs-rev))))
    (values m* (reverse xs*-rev)))

  (: new-formals! : S->S -formals → (values S->S -formals))
  (define (new-formals! m xs)
    (match xs
      [(-varargs zs z)
       (define-values (m₁ zs*) (new-binders! m zs))
       (define-values (m₂ z* ) (new-binder!  m₁ z))
       (values m₂ (-varargs zs* z*))]
      [(? list? xs) (new-binders! m xs)]))

  (define (go-m! [m : S->S] [modl : -module]) : -module
    (match-define (-module p forms) modl)
    (define forms*
      (for/list : (Listof -module-level-form) ([form forms])
        (match form
          [(-define-values xs e) (-define-values xs (go! m e))]
          [(-provide specs)
           (-provide
            (for/list ([spec specs])
              (match-define (-p/c-item x c ℓ) spec)
              (-p/c-item x (go! m c) ℓ)))]
          [(? -require? d) d]
          [(? -e? e) (go! m e)])))
    (-module p forms*))

  (define (go! [m : S->S] [e : -e]) : -e
    (match e
      [(-λ xs e*)
       (define-values (m* xs*) (new-formals! m xs))
       (-λ xs* (go! m* e*))]
      [(-case-λ clauses)
       (-case-λ
        (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([clause clauses])
          (match-define (cons xs e*) clause)
          (define-values (m* xs*) (new-binders! m xs))
          (cons xs* (go! m* e*))))]
      [(-x (? symbol? x)) (-x (hash-ref m x))]
      [(-@ f xs loc) (-@ (go! m f) (map (curry go! m) xs) loc)]
      [(-if e₀ e₁ e₂) (-if (go! m e₀) (go! m e₁) (go! m e₂))]
      [(-wcm k v b) (-wcm (go! m k) (go! m v) (go! m b))]
      [(-begin es) (-begin (map (curry go! m) es))]
      [(-begin0 e₀ es) (-begin0 (go! m e₀) (map (curry go! m) es))]
      [(-let-values bnds bod)
       (define-values (m* bnds*-rev)
         (for/fold ([m* : S->S m] [bnds*-rev : (Listof (Pairof (Listof Var-Name) -e)) '()])
                   ([bnd bnds])
           (match-define (cons xs eₓ) bnd)
           (define-values (m** xs*) (new-binders! m* xs))
           (define eₓ* (go! m #|important|# eₓ))
           (values m** (cons (cons xs* eₓ*) bnds*-rev))))
       (define bod* (go! m* bod))
       (-let-values (reverse bnds*-rev) bod*)]
      [(-letrec-values bnds bod)
       (define-values (xss es) (unzip bnds))
       (define-values (m* xss*-rev)
         (for/fold ([m* : S->S m] [xss*-rev : (Listof (Listof Var-Name)) '()])
                   ([xs xss])
           (define-values (m** xs*) (new-binders! m* xs))
           (values m** (cons xs* xss*-rev))))
       (define es* (map (curry go! m*) es))
       (define bod* (go! m* bod))
       (define bnds* (map (inst cons (Listof Var-Name) -e) (reverse xss*-rev) es*))
       (-letrec-values bnds* bod*)]
      [(-set! (? symbol? x) e*) (-set! (hash-ref m x #|when `x` is top-level|# (λ () x)) (go! m e*))]
      [(-amb es) (-amb (map/set (curry go! m) es))]
      [(-μ/c x c) (-μ/c x (go! m c))]
      [(--> cs d ℓ) (--> (map (curry go! m) cs) (go! m d) ℓ)]
      [(-->i cs mk-d ℓ)
       (-->i (map (curry go! m) cs)
             (assert (go! m mk-d) -λ?)
             ℓ)]
      [(-case-> clauses ℓ)
       (define clauses* : (Listof (Pairof (Listof -e) -e))
         (for/list ([clause clauses])
           (match-define (cons cs d) clause)
           (cons (map (curry go! m) cs) (go! m d))))
       (-case-> clauses* ℓ)]
      [(-struct/c si cs ℓ)
       (-struct/c si (map (curry go! m) cs) ℓ)]
      [_ e]))

  (cond [(-e? e) (go! (hasheq) e)]
        [else (go-m! (hasheq) e)]))


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
               (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([clause clauses])
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
            [(-let-values bnds body)
             (define-values (bnds*-rev locals)
               (for/fold ([bnds*-rev : (Listof (Pairof (Listof Var-Name) -e)) '()]
                          [locals : (℘ Var-Name) ∅eq])
                         ([bnd bnds])
                 (match-define (cons xs eₓ) bnd)
                 (values (cons (cons xs (go m eₓ)) bnds*-rev)
                         (set-add-list locals xs))))
             (define body* (go (shrink m locals) body))
             (-let-values (reverse bnds*-rev) body*)]
            [(-letrec-values bnds body)
             (define locals
               (for/fold ([locals : (℘ Var-Name) ∅eq])
                         ([bnd bnds])
                 (match-define (cons xs _) bnd)
                 (set-add-list locals xs)))
             (define m* (shrink m locals))
             (define bnds* : (Listof (Pairof (Listof Var-Name) -e))
               (for/list ([bnd bnds])
                 (match-define (cons xs eₓ) bnd)
                 (cons xs (go m* eₓ))))
             (define body* (go m* body))
             (-letrec-values bnds* body*)]
            [(-set! x e*)
             (-set! x (go m e*))]
            [(-amb es)
             (-amb (for/set: : (℘ -e) ([e es]) (go m e)))]
            [(-μ/c z c)
             (-μ/c z (go (shrink m {seteq z}) c))]
            [(--> cs d ℓ)
             (--> (go-list m cs) (go m d) ℓ)]
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

(: shrink : Subst (℘ Var-Name) → Subst)
(define (shrink m xs)
  (for/fold ([m* : Subst m])
            ([eₓ (in-hash-keys m)]
             #:unless (set-empty? (∩ xs (fv eₓ))))
    (hash-remove m* eₓ)))

(: formals->names : -formals → (℘ Var-Name))
(define (formals->names xs)
  (cond
    [(-varargs? xs) (set-add (list->seteq (-varargs-init xs)) (-varargs-rest xs))]
    [else (list->seteq xs)]))

(define (show-subst [m : Subst]) : (Listof Sexp)
  (for/list ([(k v) m]) `(,(show-e k) ↦ ,(show-e v))))
