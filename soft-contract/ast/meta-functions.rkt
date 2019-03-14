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
      [(-μ/c _ e) (fv e)]
      [(-->i (-var cs c) d)
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
        [(-μ/c x e) (if (equal? x z) 0 (go e))]
        [(-->i (-var cs c) d)
         (define dom-count : (-dom → Natural)
           (match-lambda [(-dom x _ eₓ _) (if (equal? x z) 0 (go eₓ))]))
         (+ (apply + (if c (dom-count c) 0) (map dom-count cs))
            (if d (apply + (map dom-count d)) 0))]
        [(case--> cases) (apply + (map go cases))]
        [_ 0])))

  (: free-x/c : -e → (℘ Symbol))
  ;; Return all free references to recursive contracts inside term
  (define (free-x/c e)

    (: go* (∀ (X) (X → (℘ Symbol)) → (Listof X) → (℘ Symbol)))
    (define ((go* f) xs) (apply ∪ ∅eq (map f xs)))

    (: go/dom : -dom → (℘ Symbol))
    (define go/dom
      (match-lambda
        [(-dom _ ?xs d _) (if ?xs (go (-λ (-var ?xs #f) d +ℓ₀)) (go d))]))

    (: go : -e → (℘ Symbol))
    (define (go e)
      (match e
        [(-λ xs e _) (go e)]
        [(-case-λ cases _) ((go* go) cases)]
        [(-@ f xs ctx) (∪ (go f) ((go* go) xs))]
        [(-if i t e _) (∪ (go i) (go t) (go e))]
        [(-wcm k v b) (∪ (go k) (go v) (go b))]
        [(-begin es) ((go* go) es)]
        [(-begin0 e es) (∪ (go e) ((go* go) es))]
        [(-let-values bnds e _)
         (apply ∪ (go e) (map (compose1 go Binding-rhs) bnds))]
        [(-letrec-values bnds e _)
         (apply ∪ (go e) (map (compose1 go Binding-rhs) bnds))]
        [(-μ/c _ c) (go c)]
        [(-->i (-var cs c) d)
         (∪ ((go* go/dom) cs)
            (if c (go/dom c) ∅eq)
            (if d ((go* go/dom) d) ∅eq))]
        [(case--> cases) ((go* go) cases)]
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

    (: go--->i : Subst -->i → -->i)
    (define (go--->i m c)
      (define go/dom : (-dom → -dom)
        (match-lambda
          [(-dom x ?xs d ℓ)
           (define d* (if ?xs (go (remove-keys m (list->seteq ?xs)) d) (go m d)))
           (-dom x ?xs d* ℓ)]))
      (match-define (-->i cs d) c)
      (-->i (var-map go/dom cs) (and d (map go/dom d))))

    (: go : Subst -e → -e)
    (define (go m e)
      (with-debugging/off
        ((ans)
         
         (cond
           [(hash-empty? m) e]
           [else
            (match e
              [(or (-x x _) (-x/c.tmp x))
               #:when x
               (hash-ref m x (λ () e))]
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
              [(-μ/c z c)
               (-μ/c z (go (remove-keys m {seteq z}) c))]
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

  (: optimize-contracts : (℘ ℓ) -module → -module)
  (define (optimize-contracts ℓs m)
    (match-define (-module l body) m) 
    
    ;; collect all top-level mappings
    (define top-maps
      (for/fold ([acc : (HashTable Symbol -e) (hasheq)])
                ([form (in-list body)])
        (match form
          [(-define-values (list x) e _) (hash-set acc x e)]
          [(-define-values xs (-@ 'values es _) _)
           (for/fold ([acc : (HashTable Symbol -e) acc])
                     ([x (in-list xs)] [e (in-list es)])
             (hash-set acc x e))]
          [_ acc])))
    
    (define extra-defns : (Mutable-HashTable Symbol -e) (make-hasheq))

    ;; A cache for optimization of contract references
    (define cache : (Mutable-HashTable (Pairof Boolean Symbol) -e) (make-hash))

    (define go-module-level-form : (-module-level-form → -module-level-form)
      (match-lambda ; only optimize at `provide` clause
        [(-provide specs) (-provide (map go-spec specs))]
        [form form]))

    (define go-spec : (-provide-spec → -provide-spec)
      (match-lambda
        [(-p/c-item x e ℓ)
         (-p/c-item x ((go-c #t ℓ) e) ℓ)]
        [(? symbol? s) s]))

    (define locs (set-map ℓs ℓ->loc))
    (: opt? : Boolean (Option ℓ) → Boolean)
    (define (opt? pos? ℓ)
      (and pos?
           ℓ
           ;; TODO clean up. This hack is to counter `unique` tag in `next-ℓ!`
           (match-let ([(loc s l c id) (ℓ->loc ℓ)])
             (not (ormap
                   (match-lambda
                     [(loc (== s) (== l) (== c) idᵢ) (list-prefix? idᵢ id)]
                     [_ #f])
                   locs)))
           #t))

    (: go-c : Boolean (Option ℓ) → -e → -e)
    (define ((go-c pos? ℓ*) e) 
      
      (: map-opt : (Listof -e) ℓ Symbol Symbol → (Listof -e))
      (define (map-opt es ℓ lid rid)
        (let go ([i : Natural 0] [es : (Listof -e) es])
          (match es
            [(list e₁ e₂)
             (define ℓ* (ℓ-with-id ℓ i))
             (list ((go-c pos? (ℓ-with-id ℓ* lid)) e₁)
                   ((go-c pos? (ℓ-with-id ℓ* rid)) e₂))]
            [(cons e es*)
             (cons ((go-c pos? (ℓ-with-id ℓ (list lid i))) e)
                   (go (+ 1 i) es*))]
            ['() '()])))
      
      (match e
        [(-@ 'and/c es ℓ)
         (opt-and/c (map-opt es ℓ 'left-conj 'right-conj) ℓ)]
        [(-@ 'or/c es ℓ)
         ;; Can optimize `or/c` if all of its disjuncts can be optimized
         (if (andmap any/c? (map-opt es ℓ 'left-disj 'right-disj)) 'any/c e)]
        [(-μ/c x e) (-μ/c x ((go-c pos? #f) e))]
        [(-->i doms rng)
         (-->i (var-map (go-dom (not pos?)) doms) (and rng (map (go-dom pos?) rng)))]
        [(case--> cases) (printf "TODO: opt case->~n") (case--> cases)]
        [(-if e e₁ e₂ ℓ) (-if e ((go-c pos? #f) e₁) ((go-c pos? #f) e₂) ℓ)]
        [(-wcm k v b) (-wcm k v ((go-c pos? #f) b))]
        [(-begin es) (match-let-values ([(es₀ (list eₙ)) (split-at es (sub1 (length es)))])
                       (-begin (append es₀ (list ((go-c pos? #f) eₙ)))))]
        [(-begin0 e es) (-begin0 ((go-c pos? #f) e) es)]
        [(-let-values bs e ℓ)
         (-let-values (map (go-Binding pos? #f) bs) ((go-c pos? #f) e) ℓ)]
        [(-letrec-values bs e ℓ)
         (-letrec-values (map (go-Binding pos? #f) bs) ((go-c pos? #f) e) ℓ)]
        [(? -v?) #:when (opt? pos? ℓ*) 'any/c]
        [(-x (-𝒾 (and s
                      (app (λ (s) (hash-ref top-maps s #f)) (? values c)))
                 (== l))
             ℓ)
         (hash-ref! cache (cons pos? s)
                    (λ ()
                      (define c* ((go-c pos? #f) c))
                      ;; keep reference if optimization does nothing
                      (cond
                        [(equal? c* c) e]
                        [(-o? c*) c*]
                        [else
                         (define x* (gensym s))
                         (hash-set! extra-defns x* c*)
                         (-x (-𝒾 x* l) ℓ)])))]
        [_ e]))

    (: go-Binding : Boolean (Option ℓ) → Binding → Binding)
    (define (go-Binding pos? ℓ)
      (match-lambda [(cons xs e) (cons xs ((go-c pos? ℓ) e))]))

    (: go-dom : Boolean → -dom → -dom)
    (define ((go-dom pos?) dom)
      (match-define (-dom x xs e ℓ) dom)
      (-dom x xs ((go-c pos? ℓ) e) ℓ))

    (: go-rng : Boolean → -dom → -dom)
    (define ((go-rng pos?) rng)
      (match ((go-dom pos?) rng)
        ['any/c #:when (opt? pos? (-dom-loc rng)) 'any]
        [r r]))

    (: opt-and/c : (Listof -e) ℓ → -e)
    (define (opt-and/c cs ℓ)
      (match (filter-not any/c? cs)
        [(list) 'any/c]
        [(list c) c]
        [cs* (-@ 'and/c cs* ℓ)]))
    
    (-module l (append (map go-module-level-form body)
                       (for/list : (Listof -module-level-form) ([(x e) (in-hash extra-defns)])
                         (-define-values (list x) e +ℓ₀)))))

  (: optimize-uses : (℘ ℓ) -module → -module)
  (define (optimize-uses ℓs m)

    (define go-module-level-form : (-module-level-form → -module-level-form)
      (match-lambda
        [(? -e? e) (go-e e)]
        [(-define-values xs e ℓ) (-define-values xs (go-e e) ℓ)]
        [(? -require? r) r]
        [(-provide specs) (-provide (map go-spec specs))]
        [(? -submodule-form? m) m]))

    (define go-spec : (-provide-spec → -provide-spec)
      (match-lambda
        [(-p/c-item x e ℓ) (-p/c-item x (go-e e) ℓ)]
        [(? symbol? s) s]))

    (define go-e : (-e → -e)
      (match-lambda
        [(? -λ? e) (go-λ e)]
        [(-case-λ cases ℓ) (-case-λ (map go-λ cases) ℓ)]
        [(-@ e es ℓ)
         (define es* (map go-e es))
         (if (and (-prim? e) (not (∋ ℓs ℓ)))
             (-@/unsafe e es* ℓ)
             (-@ (go-e e) es* ℓ))]
        [(-if e e₁ e₂ ℓ) (-if (go-e e) (go-e e₁) (go-e e₂) ℓ)]
        [(-wcm k v b) (-wcm (go-e k) (go-e v) (go-e b))]
        [(-begin es) (-begin (map go-e es))]
        [(-begin0 e es) (-begin0 (go-e e) (map go-e es))]
        [(-let-values bs e ℓ)
         (-let-values (map go-Binding bs) (go-e e) ℓ)]
        [(-letrec-values bs e ℓ)
         (-letrec-values (map go-Binding bs) (go-e e) ℓ)]
        [(-set! x e ℓ) (-set! x (go-e e) ℓ)]
        [(-μ/c x e) (-μ/c x (go-e e))]
        [(? -->i? c) (go--->i c)]
        [(case--> cases) (case--> (map go--->i cases))]
        [(-∀/c xs e ℓ) (-∀/c xs (go-e e) ℓ)]
        [e e]))

    (define go-λ : (-λ → -λ)
      (match-lambda [(-λ xs e ℓ) (-λ xs (go-e e) ℓ)]))

    (define go--->i : (-->i → -->i)
      (match-lambda
        [(-->i doms rng) (-->i (var-map go-dom doms) (and rng (map go-dom rng)))]))

    (define go-Binding : (Binding → Binding)
      (match-lambda [(cons xs e) (cons xs (go-e e))]))

    (define go-dom : (-dom → -dom)
      (match-lambda [(-dom x xs e ℓ) (-dom x xs (go-e e) ℓ)]))

    (: -@/unsafe : -prim (Listof -e) ℓ → -e)
    (define (-@/unsafe o xs ℓ)
      (match o
        [(app unsafe-op (? values o*)) (-@ o* xs ℓ)]
        [(-st-ac _ i ) (-@ 'unsafe-struct-ref  (append xs (list (-b i))) ℓ)]
        [(-st-mut _ i) (-@ 'unsafe-struct-set! (append xs (list (-b i))) ℓ)]
        [o (-@ o xs ℓ)]))

    (define unsafe-op : (-prim → (Option -prim))
      (match-lambda
        [(== -car) 'unsafe-car]
        [(== -cdr) 'unsafe-cdr]
        [(== -set-mcar!) 'unsafe-set-mcar!]
        [(== -set-mcdr!) 'unsafe-set-mcdr!]
        [(== -unbox) 'unsafe-unbox]
        [(== -set-box!) 'unsafe-set-box!]
        ['string-length 'unsafe-string-length]
        ['string-ref 'unsafe-string-ref]
        ['string-set! 'unsafe-string-set!]
        ['vector-length 'unsafe-vector-length]
        ['vector-ref 'unsafe-vector-ref]
        ['vector-set! 'unsafe-vector-set!]
        [o #|TODO more|# #f]))
    
    (match-define (-module l body) m)
    (-module l (map go-module-level-form body)))

  (define (any/c? x) (equal? x 'any/c))
  
  )
