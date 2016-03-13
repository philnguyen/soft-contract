#lang typed/racket/base

(provide
 fv 𝐴 closed? checks# free-x/c e/ e/map e/fun e/list unroll find-calls prim-name->unsafe-prim
 opq-exp? α-rename)

(require
 racket/match racket/set racket/function
 "../utils/main.rkt" "../utils/untyped-macros.rkt" "definition.rkt")

(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)])
(require/typed racket/base
  [hash-empty? ((HashTable -e -e) → Boolean)])

(: fv : (U -e (Listof -e)) → (Setof Symbol))
;; Compute free variables for expression. Return set of variable names.
(define (fv e)
  (match e
    [(-x x) {set x}]
    [(-λ xs e)
     (define bound
       (match xs
         [(-varargs zs z) (set-add (list->set zs) z)]
         [(? list? xs) (list->set xs)]))
     (-- (fv e) bound)]
    [(-@ f xs _)
     (for/fold ([FVs (fv f)]) ([x xs]) (∪ FVs (fv x)))]
    [(-begin es) (fv es)]
    [(-begin0 e₀ es) (∪ (fv e₀) (fv es))]
    [(-let-values bnds e _)
     (define-values (bound FV_rhs)
       (for/fold ([bound : (Setof Symbol) ∅] [FV_rhs : (Setof Symbol) ∅]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ FV_rhs (fv rhs)))))
     (∪ FV_rhs (-- (fv e) bound))]
    [(-letrec-values bnds e _)
     (define bound
       (for/fold ([bound : (Setof Symbol) ∅]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     
     (for/fold ([xs : (Setof Symbol) (-- (fv e) bound)]) ([bnd bnds])
       (-- (fv (cdr bnd)) bound))]
    [(-set! x e) (set-add (fv e) x)]
    [(-@-havoc x) (fv x)]
    #;[(.apply f xs _) (set-union (fv f d) (fv xs d))]
    [(-if e e₁ e₂) (∪ (fv e) (fv e₁) (fv e₂))]
    [(-amb es)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e es])
       (∪ xs (fv e)))]
    [(-μ/c _ e) (fv e)]
    [(-->i cs mk-d _) (apply ∪ (fv mk-d) (map fv cs))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (Setof Symbol) ∅]) ([c cs])
       (∪ xs (fv c)))]
    [(? list? l)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e l])
       (∪ xs (fv e)))]
    [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅]))

(module+ test
  (require typed/rackunit)
  
  (check-equal? (fv -tt) ∅)
  (check-equal? (fv (-λ '(x) (-x 'x))) ∅)
  (check-equal? (fv (-x 'x)) {set 'x})
  (check-equal? (fv (-ref (-id 'cons 'Λ) 'l 0)) ∅)
  (check-equal? (fv (-λ '(x) (-λ '(y) (-@ (-x 'f) (list (-x 'y) (-x 'x)) -Λ)))) {set 'f}))

(: 𝐴 : (U -e (Listof -e)) → (Setof Symbol))
;; Collect all asignable free variables
(define (𝐴 e)
  (match e
    [(-x x) ∅]
    [(-λ xs e)
     (define bound
       (match xs
         [(-varargs zs z) (set-add (list->set zs) z)]
         [(? list? xs) (list->set xs)]))
     (-- (𝐴 e) bound)]
    [(-@ f xs _)
     (for/fold ([𝐴s (𝐴 f)]) ([x xs]) (∪ 𝐴s (𝐴 x)))]
    [(-begin es) (𝐴 es)]
    [(-begin0 e₀ es) (∪ (𝐴 e₀) (𝐴 es))]
    [(-let-values bnds e _)
     (define-values (bound 𝐴_rhs)
       (for/fold ([bound : (Setof Symbol) ∅] [𝐴_rhs : (Setof Symbol) ∅]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ 𝐴_rhs (𝐴 rhs)))))
     (∪ 𝐴_rhs (-- (𝐴 e) bound))]
    [(-letrec-values bnds e _)
     (define bound
       (for/fold ([bound : (Setof Symbol) ∅]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     (for/fold ([xs : (Setof Symbol) (-- (𝐴 e) bound)]) ([bnd bnds])
       (-- (𝐴 (cdr bnd)) bound))]
    [(-set! x e) (set-add (𝐴 e) x)]
    [(-@-havoc x) ∅]
    #;[(.apply f xs _) (set-union (𝐴 f d) (𝐴 xs d))]
    [(-if e e₁ e₂) (∪ (𝐴 e) (𝐴 e₁) (𝐴 e₂))]
    [(-amb es)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e es])
       (∪ xs (𝐴 e)))]
    [(-μ/c _ e) (𝐴 e)]
    [(-->i cs mk-d _) (apply ∪ (𝐴 mk-d) (map 𝐴 cs))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (Setof Symbol) ∅]) ([c cs])
       (∪ xs (𝐴 c)))]
    [(? list? l)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e l])
       (∪ xs (𝐴 e)))]
    [_ (log-debug "𝐴⟦~a⟧ = ∅~n" e) ∅]))

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
                       -prog
                       (Listof X))) → Integer)
;; Statically count number of unsafe operations needing checks
(define checks#
  (match-lambda
   [(? list? es) (for/sum : Integer ([e (in-list es)]) (checks# e))]
   [(-prog ms e) (+ (checks# ms) (checks# e))]
   [(-define-values _ _ e) (checks# e)]
   [(-λ _ e) (checks# e)]
   [(-@ f xs _) (+ 1 (checks# f) (checks# xs))]
   [(-if i t e) (+ (checks# i) (checks# t) (checks# e))]
   [(-wcm k v e) (+ (checks# k) (checks# v) (checks# e))]
   [(-begin0 e es) (+ (checks# e) (checks# es))]
   [(-let-values bindings e _)
    (+ (for/sum : Integer ([binding (in-list bindings)])
         (match-define (cons _ eₓ) binding)
         (checks# eₓ))
       (checks# e))]
   [(-letrec-values bindings e _)
    (+ (for/sum : Integer ([binding (in-list bindings)])
         (match-define (cons _ eₓ) binding)
         (checks# eₓ))
       (checks# e))]
   [(-amb es) (for/sum ([e (in-set es)]) (checks# e))]
   [(-μ/c _ c) (checks# c)]
   [(-->i cs mk-d _) (+ (checks# cs) (checks# mk-d))]
   [(-struct/c _ cs _) (checks# cs)]

   [(-module _ body) (checks# body)]
   ;; FIXME count up for primitives
   [_ 0]))

(: free-x/c : -e → (Setof Symbol))
;; Return all free references to recursive contracts inside term
(define (free-x/c e)

  (: go* : (Listof -e) → (Setof Symbol))
  (define (go* xs) (for/union : (Setof Symbol) ([x xs]) (go x)))

  (: go : -e → (Setof Symbol))
  (define (go e)
    (match e
      [(-λ xs e) (go e)]
      [(-case-λ body)
       (for/union : (Setof Symbol) ([p body]) (go (cdr p)))]
      [(-@ f xs ctx) (∪ (go f) (go* xs))]
      [(-if i t e) (∪ (go i) (go t) (go e))]
      [(-wcm k v b) (∪ (go k) (go v) (go b))]
      [(-begin0 e es) (∪ (go e) (go* es))]
      [(-let-values bnds e ctx)
       (∪ (for/union : (Setof Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-letrec-values bnds e ctx)
       (∪ (for/union : (Setof Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-amb es) (for/union : (Setof Symbol) ([e es]) (go e))]
      [(-μ/c _ c) (go c)]
      [(-->i cs mk-d _) (∪ (go* cs) (go mk-d))]
      [(-struct/c t cs _) (go* cs)]
      [(-x/c.tmp x) (set x)]
      [_ ∅]))
  
  (go e))

(: e/ : -e -e -e → -e)
;; Substitution, where `x` can be an (open) term rather than just a free variable.
(define (e/ x eₓ e)
  ((e/map (hash x eₓ)) e))

(: e/list : (Listof -e) (Listof -e) -e → -e)
;; Simultaneous subtitution
(define (e/list xs exs e)
  (define m
    (for/hash : (HashTable -e -e) ([x xs] [ex exs])
      (values x ex)))
  ((e/map m) e))

(: e/map : (HashTable -e -e) → -e → -e)
(define ((e/map m) e)
  (let go ([m m] [e e])
    (cond
      [(hash-empty? m) e]
      [(hash-ref m e #f) => values]
      [else
       (match e
         [(-λ xs e*) (-λ xs (go (shrink m xs) e*))]
         [(-case-λ clauses)
          (-case-λ
           (for/list : (Listof (Pairof -formals -e)) ([clause clauses])
             (match-define (cons xs e*) clause)
             (cons xs (go (shrink m xs) e*))))]
         [(? -v?) e]
         [(? -ref?) e]
         [(-@ f xs l) (-@ (go m f) (map (curry go m) xs) l)]
         [(-if e₀ e₁ e₂) (-if (go m e₀) (go m e₁) (go m e₂))]
         [(-wcm k v b) (-wcm (go m k) (go m v) (go m b))]
         [(-begin0 e₀ es) (-begin0 (go m e₀) (map (curry go m) es))]
         [(? -quote?) e]
         [(-let-values bnds e* l)
          (define-values (bnds-rev locals)
            (for/fold ([bnds-rev : (Listof (Pairof (Listof Symbol) -e)) '()]
                       [locals : (Setof Symbol) ∅])
                      ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (values (cons (cons xs (go m ex)) bnds-rev)
                      (set-add-list locals xs))))
          (define m* (shrink m (set->list locals)))
          (-let-values (reverse bnds-rev) (go m* e*) l)]
         [(-letrec-values bnds e* l)
          (define xs
            (set->list
             (for/fold ([locals : (Setof Symbol) ∅]) ([bnd bnds])
               (set-add-list locals (car bnd)))))
          (define m* (shrink m xs))
          (define bnds*
            (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (cons xs (go m* ex))))
          (-letrec-values bnds* (go m* e*) l)]
         [(-set! z e*) (-set! z (go m e*))]
         [(-amb es) (-amb (map/set (curry go m) es))]
         [(-μ/c z c) (-μ/c z (go m c))]
         [(-->i cs mk-d pos)
          (-->i (map (curry go m) cs)
                (assert (go m mk-d) -λ?)
                pos)]
         [(-struct/c t cs p) (-struct/c t (map (curry go m) cs) p)]
         [_
          (log-debug "e/: ignore substituting ~a" (show-e e))
          e])])))

(: e/fun : (-e → (Option -e)) → -e → -e)
;; Duplicate code as `e/map` for now for some efficiency of `e/map`
(define ((e/fun f) e)

  (let go ([f f] [e e])
    (cond
      [(f e) => values]
      [else
       (match e
         [(-λ xs e*) (-λ xs (go (shrink-f f xs) e*))]
         [(-case-λ clauses)
          (-case-λ
           (for/list : (Listof (Pairof -formals -e)) ([clause clauses])
             (match-define (cons xs e*) clause)
             (cons xs (go (shrink-f f xs) e*))))]
         [(? -v?) e]
         [(? -ref?) e]
         [(-@ g xs l) (-@ (go f g) (map (curry go f) xs) l)]
         [(-if e₀ e₁ e₂) (-if (go f e₀) (go f e₁) (go f e₂))]
         [(-wcm k v b) (-wcm (go f k) (go f v) (go f b))]
         [(-begin0 e₀ es) (-begin0 (go f e₀) (map (curry go f) es))]
         [(? -quote?) e]
         [(-let-values bnds e* l)
          (define-values (bnds-rev locals)
            (for/fold ([bnds-rev : (Listof (Pairof (Listof Symbol) -e)) '()]
                       [locals : (Setof Symbol) ∅])
                      ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (values (cons (cons xs (go f ex)) bnds-rev)
                      (set-add-list locals xs))))
          (define f* (shrink-f f (set->list locals)))
          (-let-values (reverse bnds-rev) (go f* e*) l)]
         [(-letrec-values bnds e* l)
          (define xs
            (set->list
             (for/fold ([locals : (Setof Symbol) ∅]) ([bnd bnds])
               (set-add-list locals (car bnd)))))
          (define f* (shrink-f f xs))
          (define bnds*
            (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (cons xs (go f* ex))))
          (-letrec-values bnds* (go f* e*) l)]
         [(-set! z e*) (-set! z (go f e*))]
         [(-amb es) (-amb (map/set (curry go f) es))]
         [(-μ/c z c) (-μ/c z (go f c))]
         [(-->i cs mk-d pos)
          (-->i (map (curry go f) cs)
                (assert (go f mk-d) -λ?)
                pos)]
         [(-struct/c t cs p) (-struct/c t (map (curry go f) cs) p)]
         [_
          (log-debug "e/: ignore substituting ~a" e)
          e])])))

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
      [(-case-λ clauses) (-case-λ (map (inst go-bnd -formals) clauses))]
      [(-@ f xs l) (-@ (go f) (map go xs) l)]
      [(-if e₀ e₁ e₂) (-if (go e₀) (go e₁) (go e₂))]
      [(-wcm k v b) (-wcm (go k) (go v) (go b))]
      [(-begin0 e₀ es) (-begin0 (go e₀) (map go es))]
      [(-let-values bnds e* l)
       (-let-values (map (inst go-bnd (Listof Symbol)) bnds) (go e*) l)]
      [(-letrec-values bnds e* l)
       (-letrec-values (map (inst go-bnd (Listof Symbol)) bnds) (go e*) l)]
      [(-set! z e*) (-set! z (go e*))]
      [(-amb es) (-amb (map/set go es))]
      [(-μ/c z e*) (if (= z x) e (-μ/c z (go e*)))]
      [(-->i cs mk-d pos)
       (-->i (map go cs) (assert (go mk-d) -λ?) pos)]
      [(-struct/c si cs pos) (-struct/c si (map go cs) pos)]
      [(-x/c z) (if (= z x) c e)]
      [_
       (log-debug "unroll: ignore ~a" (show-e e))
       e])))


;; Shrink domain of `m` to not be included by `xs`
(define (shrink [m : (HashTable -e -e)] [xs : -formals]) : (HashTable -e -e)
  (for/fold ([m* : (HashTable -e -e) m])
            ([x (in-hash-keys m)] #:when (binder-has? xs x))
    (hash-remove m* x)))

(define (shrink-f [f : (-e → (Option -e))] [xs : -formals]) : (-e → (Option -e))
  (define shadows
    (match xs
      [(-varargs zs z) (set-add (list->set zs) z)]
      [(? list?) (list->set xs)]))
  (λ (e) (and (set-empty? (∩ shadows (fv e))) (f e))))

(: find-calls : -e (U -id -•) → (Setof (Listof -e)))
;; Search for all invocations of `f-id` in `e`
(define (find-calls e f-id)
  (define-set calls : (Listof -e))
  (let go : Void ([e e])
    (match e
      [(-@ f xs _)
       (go f)
       (for-each go xs)
       (when (match? f (-ref (== f-id) _ _) (== f-id))
         (calls-add! xs))]
      [_ (void)]))
  calls)

(: -formals-names : -formals → (Setof Symbol))
;; Return all names that a formal list binds
(define -formals-names
  (match-lambda
    [(-varargs xs x) (set-add (list->set xs) x)]
    [(? list? xs) (list->set xs)]))

(: binder-has? : -formals (U Symbol -e) → (Option (Setof Symbol)))
;; returns whether a list of binding names has given name
(define (binder-has? xs x)
  (define FVs (if (symbol? x) {set x} (fv x)))
  (define captured (∩ FVs (-formals-names xs)))
  (and (not (set-empty? captured)) captured))

(: prim-name->unsafe-prim : Symbol → -o)
;; Convert primitive name to (unsafe) primitive
(define prim-name->unsafe-prim
  (let ([specials : (HashTable Symbol -o) (make-hasheq)]
        [aliases : (HashTable Symbol Symbol) (make-hasheq)]
        [mk-struct-info : (Any → -struct-info)
         (match-lambda
           [`(,(? symbol? t) ,(? boolean? bs) ...)
            (-struct-info (-id t 'Λ)
                          (length bs)
                          (for/set: : (Setof Integer) ([(b i) (in-indexed bs)] #:when b) i))])])
    (for ([dec prims])
      (match dec
        [`(#:alias ,(? symbol? x) ,(? symbol? y))
         (hash-set! aliases x y)]
        [`(#:struct-cons ,(? symbol? x) ,si)
         (hash-set! specials x (-st-mk (mk-struct-info si)))]
        [`(#:struct-pred ,(? symbol? x) ,si)
         (hash-set! specials x (-st-p (mk-struct-info si)))]
        [`(#:struct-acc ,(? symbol? x) ,si ,(? exact-integer? i))
         (hash-set! specials x (-st-ac (mk-struct-info si) i))]
        [`(#:struct-acc ,(? symbol? x) ,si ,(? exact-integer? i))
         (hash-set! specials x (-st-mut (mk-struct-info si) i))]
        [_ (void)]))
    (λ (x)
      (cond
        [(hash-ref specials x #f)]
        [(hash-ref aliases x #f) => prim-name->unsafe-prim]
        [else x]))))

(: opq-exp? : -e → Boolean)
;; Check if expression has •
(define (opq-exp? e)
  (match e
    [(? -•?) #t]
    [(-if e₁ e₂ e₃) (or (opq-exp? e₁) (opq-exp? e₂) (opq-exp? e₃))]
    [(-wcm k v b) (or (opq-exp? k) (opq-exp? v) (opq-exp? b))]
    [(-begin0 e₀ es) (or (opq-exp? e₀) (ormap opq-exp? es))]
    [(-let-values _ b _) (opq-exp? b)]
    [(-letrec-values _ b _) (opq-exp? b)]
    [(-set! _ e*) (opq-exp? e*)]
    [(-@ f xs _) (or (opq-exp? f) (ormap opq-exp? xs))]
    [_ #f]))

(: α-rename : -e → -e)
;; Make sure each binding has a unique name
(define (α-rename e)
  (define-type S->S (HashTable Symbol Symbol))
  ;; Map each bound name to its ith appearance. `0` means first, no need to rename
  (define ith : (HashTable Symbol Natural) (make-hasheq))

  (: new-binder! : S->S Symbol → (Values S->S Symbol))
  (define (new-binder! names x)
    (cond
      [(hash-ref ith x #f) =>
       (λ (i) (hash-set! ith x (+ 1 i)))]
      [else (hash-set! ith x 0)])
    (define x*
      (match (hash-ref ith x)
        [0 x]
        [i (string->symbol (format "~a~a" x (n-sub i)))]))
    (values (hash-set names x x*) x*))

  (: new-binders! : S->S (Listof Symbol) → (Values S->S (Listof Symbol)))
  (define (new-binders! m xs)
    (define-values (m* xs*-rev)
      (for/fold ([m* : S->S m] [xs*-rev : (Listof Symbol) '()])
                ([x xs])
        (define-values (m** x*) (new-binder! m* x))
        (values m** (cons x* xs*-rev))))
    (values m* (reverse xs*-rev)))

  (: new-formals! : S->S -formals → (values S->S -formals))
  (define (new-formals! m xs)
    (match xs
      [(-varargs zs z)
       (define-values (m₁ zs*) (new-binders! m zs))
       (define-values (m₂ z*) (new-binder! m₁ z))
       (values m₂ (-varargs zs* z*))]
      [(? list? xs) (new-binders! m xs)]))

  (let go! ([m : S->S (hasheq)] [e : -e e])
    (match e
      [(-λ xs e*)
       (define-values (m* xs*) (new-formals! m xs))
       (-λ xs* (go! m* e*))]
      [(-case-λ clauses)
       (-case-λ
        (for/list : (Listof (Pairof -formals -e)) ([clause clauses])
          (match-define (cons xs e*) clause)
          (define-values (m* xs*) (new-formals! m xs))
          (cons xs* (go! m* e*))))]
      [(-x x) (-x (hash-ref m x))]
      [(-@ f xs loc) (-@ (go! m f) (map (curry go! m) xs) loc)]
      [(-if e₀ e₁ e₂) (-if (go! m e₀) (go! m e₁) (go! m e₂))]
      [(-wcm k v b) (-wcm (go! m k) (go! m v) (go! m b))]
      [(-begin es) (-begin (map (curry go! m) es))]
      [(-begin0 e₀ es) (-begin0 (go! m e₀) (map (curry go! m) es))]
      [(-let-values bnds bod ctx)
       (define-values (m* bnds*-rev)
         (for/fold ([m* : S->S m] [bnds*-rev : (Listof (Pairof (Listof Symbol) -e)) '()])
                   ([bnd bnds])
           (match-define (cons xs eₓ) bnd)
           (define-values (m** xs*) (new-binders! m* xs))
           (define eₓ* (go! m #|important|# eₓ))
           (values m** (cons (cons xs* eₓ*) bnds*-rev))))
       (define bod* (go! m* bod))
       (-let-values (reverse bnds*-rev) bod* ctx)]
      [(-letrec-values bnds bod ctx)
       (define-values (xss es) (unzip bnds))
       (define-values (m* xss*-rev)
         (for/fold ([m* : S->S m] [xss*-rev : (Listof (Listof Symbol)) '()])
                   ([xs xss])
           (define-values (m** xs*) (new-binders! m* xs))
           (values m** (cons xs* xss*-rev))))
       (define es* (map (curry go! m*) es))
       (define bod* (go! m* bod))
       (define bnds* (map (inst cons (Listof Symbol) -e) (reverse xss*-rev) es*))
       (-letrec-values bnds* bod* ctx)]
      [(-set! x e*) (-set! (hash-ref m x) (go! m e*))]
      [(-@-havoc (-x x)) (-@-havoc (-x (hash-ref m x)))]
      [(-amb es) (-amb (map/set (curry go! m) es))]
      [(-μ/c x c) (-μ/c x (go! m c))]
      [(-->i cs mk-d pos)
       (-->i (map (curry go! m) cs)
             (assert (go! m mk-d) -λ?)
             pos)]
      [(-struct/c si cs pos)
       (-struct/c si (map (curry go! m) cs) pos)]
      [_ e])))

