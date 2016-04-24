#lang typed/racket/base

(provide
 fv 𝐴 closed? checks# free-x/c e/ e/map e/map* e/fun e/list unroll find-calls prim-name->unsafe-prim
 α-rename e-map-union -@/simp)

(require racket/match
         racket/set
         racket/function
         racket/bool
         (except-in racket/list remove-duplicates)
         racket/math
         racket/flonum
         racket/extflonum
         racket/string
         racket/function
         "../utils/main.rkt"
         "../utils/untyped-macros.rkt"
         "definition.rkt"
         (for-syntax racket/base
                     racket/contract
                     racket/match
                     (except-in racket/list remove-duplicates)
                     racket/function
                     "../utils/main.rkt"
                     (prefix-in prims: "../primitives/declarations.rkt")
                     "../primitives/utils.rkt"))

(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)])
(require/typed racket/base
  [hash-empty? ((HashTable -e -e) → Boolean)])

(: fv : (U -e (Listof -e)) → (℘ Var-Name))
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
    [(-let-values bnds e)
     (define-values (bound FV_rhs)
       (for/fold ([bound : (℘ Var-Name) ∅] [FV_rhs : (℘ Var-Name) ∅]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ FV_rhs (fv rhs)))))
     (∪ FV_rhs (-- (fv e) bound))]
    [(-letrec-values bnds e)
     (define bound
       (for/fold ([bound : (℘ Var-Name) ∅]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     
     (for/fold ([xs : (℘ Var-Name) (-- (fv e) bound)]) ([bnd bnds])
       (-- (fv (cdr bnd)) bound))]
    [(-set! x e) (set-add (fv e) x)]
    #;[(.apply f xs _) (set-union (fv f d) (fv xs d))]
    [(-if e e₁ e₂) (∪ (fv e) (fv e₁) (fv e₂))]
    [(-amb es)
     (for/fold ([xs : (℘ Var-Name) ∅]) ([e es])
       (∪ xs (fv e)))]
    [(-μ/c _ e) (fv e)]
    [(--> cs d _) (apply ∪ (fv d) (map fv cs))]
    [(-->i cs mk-d _) (apply ∪ (fv mk-d) (map fv cs))]
    [(-case-> clauses _)
     (for/union : (℘ Var-Name) ([clause clauses])
       (match-define (cons cs d) clause)
       (apply ∪ (fv d) (map fv cs)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (℘ Var-Name) ∅]) ([c cs])
       (∪ xs (fv c)))]
    [(? list? l)
     (for/fold ([xs : (℘ Var-Name) ∅]) ([e l])
       (∪ xs (fv e)))]
    [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅]))

(module+ test
  (require typed/rackunit)
  
  (check-equal? (fv -tt) ∅)
  (check-equal? (fv (-λ '(x) (-x 'x))) ∅)
  (check-equal? (fv (-x 'x)) {set 'x})
  (check-equal? (fv (-𝒾 'cons 'Λ)) ∅)
  (check-equal? (fv (-λ '(x) (-λ '(y) (-@ (-x 'f) (list (-x 'y) (-x 'x)) 0)))) {set 'f}))

(: 𝐴 : (U -e (Listof -e)) → (℘ Var-Name))
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
    [(-let-values bnds e)
     (define-values (bound 𝐴_rhs)
       (for/fold ([bound : (℘ Var-Name) ∅] [𝐴_rhs : (℘ Var-Name) ∅]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ 𝐴_rhs (𝐴 rhs)))))
     (∪ 𝐴_rhs (-- (𝐴 e) bound))]
    [(-letrec-values bnds e)
     (define bound
       (for/fold ([bound : (℘ Var-Name) ∅]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     (for/fold ([xs : (℘ Var-Name) (-- (𝐴 e) bound)]) ([bnd bnds])
       (-- (𝐴 (cdr bnd)) bound))]
    [(-set! x e) (set-add (𝐴 e) x)]
    #;[(.apply f xs _) (set-union (𝐴 f d) (𝐴 xs d))]
    [(-if e e₁ e₂) (∪ (𝐴 e) (𝐴 e₁) (𝐴 e₂))]
    [(-amb es)
     (for/fold ([xs : (℘ Var-Name) ∅]) ([e es])
       (∪ xs (𝐴 e)))]
    [(-μ/c _ e) (𝐴 e)]
    [(--> cs d _) (apply ∪ (fv d) (map fv cs))]
    [(-->i cs mk-d _) (apply ∪ (𝐴 mk-d) (map 𝐴 cs))]
    [(-case-> clauses _)
     (for/union : (℘ Var-Name) ([clause clauses])
       (match-define (cons cs d) clause)
       (apply ∪ (𝐴 d) (map 𝐴 cs)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (℘ Var-Name) ∅]) ([c cs])
       (∪ xs (𝐴 c)))]
    [(? list? l)
     (for/fold ([xs : (℘ Var-Name) ∅]) ([e l])
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
  (define (go* xs) (for/union : (℘ Symbol) ([x xs]) (go x)))

  (: go : -e → (℘ Symbol))
  (define (go e)
    (match e
      [(-λ xs e) (go e)]
      [(-case-λ body)
       (for/union : (℘ Symbol) ([p body]) (go (cdr p)))]
      [(-@ f xs ctx) (∪ (go f) (go* xs))]
      [(-if i t e) (∪ (go i) (go t) (go e))]
      [(-wcm k v b) (∪ (go k) (go v) (go b))]
      [(-begin0 e es) (∪ (go e) (go* es))]
      [(-let-values bnds e)
       (∪ (for/union : (℘ Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-letrec-values bnds e)
       (∪ (for/union : (℘ Symbol) ([bnd bnds]) (go (cdr bnd))) (go e))]
      [(-amb es) (for/union : (℘ Symbol) ([e es]) (go e))]
      [(-μ/c _ c) (go c)]
      [(--> cs d _) (∪ (go* cs) (go d))]
      [(-->i cs mk-d _) (∪ (go* cs) (go mk-d))]
      [(-case-> clauses _)
       (for/union : (℘ Symbol) ([clause clauses])
         (match-define (cons cs d) clause)
         (∪ (go d) (go* cs)))]
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
  (with-debugging/off
    ((eₐ)
     (let go : -e ([m m] [e e])
       (cond
         [(hash-empty? m) e]
         [(hash-ref m e #f) => values]
         [else
          (match e
            [(-λ xs e*) (-λ xs (go (shrink m xs) e*))]
            [(-case-λ clauses)
             (-case-λ
              (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([clause clauses])
                (match-define (cons xs e*) clause)
                (cons xs (go (shrink m xs) e*))))]
            [(? -v?) e]
            [(? -𝒾?) e]
            [(-@ f xs _) (apply -@/simp (go m f) (map (curry go m) xs))]
            [(-if e₀ e₁ e₂) (-if (go m e₀) (go m e₁) (go m e₂))]
            [(-wcm k v b) (-wcm (go m k) (go m v) (go m b))]
            [(-begin0 e₀ es) (-begin0 (go m e₀) (map (curry go m) es))]
            [(? -quote?) e]
            [(-let-values bnds e*)
             (define-values (bnds-rev locals)
               (for/fold ([bnds-rev : (Listof (Pairof (Listof Var-Name) -e)) '()]
                          [locals : (℘ Var-Name) ∅])
                         ([bnd bnds])
                 (match-define (cons xs ex) bnd)
                 (values (cons (cons xs (go m ex)) bnds-rev)
                         (set-add-list locals xs))))
             (define m* (shrink m (set->list locals)))
             (-let-values (reverse bnds-rev) (go m* e*))]
            [(-letrec-values bnds e*)
             (define xs
               (set->list
                (for/fold ([locals : (℘ Var-Name) ∅]) ([bnd bnds])
                  (set-add-list locals (car bnd)))))
             (define m* (shrink m xs))
             (define bnds*
               (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([bnd bnds])
                 (match-define (cons xs ex) bnd)
                 (cons xs (go m* ex))))
             (-letrec-values bnds* (go m* e*))]
            [(-set! z e*) (-set! z (go m e*))]
            [(-amb es) (-amb (map/set (curry go m) es))]
            [(-μ/c z c) (-μ/c z (go m c))]
            [(--> cs d ℓ) (--> (map (curry go m) cs) (go m d) ℓ)]
            [(-->i cs mk-d ℓ)
             (-->i (map (curry go m) cs)
                   (assert (go m mk-d) -λ?)
                   ℓ)]
            [(-case-> clauses ℓ)
             (define clauses* : (Listof (Pairof (Listof -e) -e))
               (for/list ([clause clauses])
                 (match-define (cons cs d) clause)
                 (cons (map (curry go m) cs) (go m d))))
             (-case-> clauses* ℓ)]
            [(-struct/c t cs p) (-struct/c t (map (curry go m) cs) p)]
            [_
             (log-debug "e/: ignore substituting ~a" (show-e e))
             e])])))
    (printf "e/map: ~a~n"
            (for/list : (Listof Sexp) ([(x y) m])
              `(,(show-e x) ↦ ,(show-e y))))
    (printf "  - from: ~a~n" (show-e e))
    (printf "  - to  : ~a~n" (show-e eₐ))
    (printf "~n")))

(: e/map* : (HashTable -e -e) → -e → -e)
;; Repeatedly substitute until it's fixed. May not terminate. Use with care.
(define ((e/map* m) e)
  (define f (e/map m))
  (with-debugging/off
    ((ans)
     (let loop : -e ([e : -e e])
       (define e* (f e))
       (if (equal? e* e) e (loop e*))))
    (printf "e/map*~n")
    (printf "  - map:~n")
    (for ([r (show-e-map m)])
      (printf "    + ~a~n" r))
    (printf "  - from: ~a~n" (show-e e))
    (printf "  - to  : ~a~n" (show-e ans))
    (printf "~n")))

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
           (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([clause clauses])
             (match-define (cons xs e*) clause)
             (cons xs (go (shrink-f f xs) e*))))]
         [(? -v?) e]
         [(? -𝒾?) e]
         [(-@ g xs l) (-@ (go f g) (map (curry go f) xs) l)]
         [(-if e₀ e₁ e₂) (-if (go f e₀) (go f e₁) (go f e₂))]
         [(-wcm k v b) (-wcm (go f k) (go f v) (go f b))]
         [(-begin0 e₀ es) (-begin0 (go f e₀) (map (curry go f) es))]
         [(? -quote?) e]
         [(-let-values bnds e*)
          (define-values (bnds-rev locals)
            (for/fold ([bnds-rev : (Listof (Pairof (Listof Var-Name) -e)) '()]
                       [locals : (℘ Var-Name) ∅])
                      ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (values (cons (cons xs (go f ex)) bnds-rev)
                      (set-add-list locals xs))))
          (define f* (shrink-f f (set->list locals)))
          (-let-values (reverse bnds-rev) (go f* e*))]
         [(-letrec-values bnds e*)
          (define xs
            (set->list
             (for/fold ([locals : (℘ Var-Name) ∅]) ([bnd bnds])
               (set-add-list locals (car bnd)))))
          (define f* (shrink-f f xs))
          (define bnds*
            (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (cons xs (go f* ex))))
          (-letrec-values bnds* (go f* e*))]
         [(-set! z e*) (-set! z (go f e*))]
         [(-amb es) (-amb (map/set (curry go f) es))]
         [(-μ/c z c) (-μ/c z (go f c))]
         [(--> cs d ℓ) (--> (map (curry go f) cs) (go f d) ℓ)]
         [(-->i cs mk-d ℓ)
          (-->i (map (curry go f) cs)
                (assert (go f mk-d) -λ?)
                ℓ)]
         [(-case-> clauses ℓ)
          (define clauses* : (Listof (Pairof (Listof -e) -e))
            (for/list ([clause clauses])
              (match-define (cons cs d) clause)
              (cons (map (curry go f) cs) (go f d))))
          (-case-> clauses* ℓ)]
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

(: -formals-names : -formals → (℘ Var-Name))
;; Return all names that a formal list binds
(define -formals-names
  (match-lambda
    [(-varargs xs x) (set-add (list->set xs) x)]
    [(? list? xs) (list->set xs)]))

(: binder-has? : -formals (U Var-Name -e) → (Option (℘ Var-Name)))
;; returns whether a list of binding names has given name
(define (binder-has? xs x)
  (define FVs (if (Var-Name? x) {set x} (fv x)))
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
      [(-set! (? symbol? x) e*) (-set! (hash-ref m x) (go! m e*))]
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

(: e-map-union : (HashTable -e -e) (HashTable -e -e) → (HashTable -e -e))
(define (e-map-union m δm)
  (for/fold ([m : (HashTable -e -e) m])
            ([(x y) δm])
    (cond
      [(hash-ref m x #f) =>
       (λ (y*)
         (unless (equal? y* y)
           (log-warning "e-map-union: ~a ↦ ~a, updated to ~a~n" (show-e x) (show-e y*) (show-e y))))])
    (hash-set m x y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper syntax definition(s) for `-@/simp`
(begin-for-syntax

  (define/contract (general-primitive-clauses f xs)
    (identifier? identifier? . -> . (listof syntax?))

    (define default-case (datum->syntax f '(default-case)))

    (define/contract (go dec)
      (any/c . -> . (listof syntax?))
      (match dec
        [`(#:pred ,(? symbol? s))
         (go `(,s (any/c . -> . boolean?) #:other-errors))]
        [`(#:pred ,(? symbol? s) (,(? prims:ctc? cs) ...))
         (go `(,s (,@cs . -> . boolean?) #:other-errors))]
        [`(#:batch (,(? symbol? ss) ...) ,(? prims:arr? c) ,_ ...)
         (append-map (λ (s) (go `(,s ,c #:other-errors))) ss)]
        [`(,(and (? symbol?) (not (? ignore-for-now?)) o) (,cs ... . -> . ,d) ,_ ...)

         (cond
           [(or (base? o) (and (andmap base? cs) (base? d)))
            
            (define/contract b-syms (listof symbol?)
              (build-list (length cs) (λ (i) (string->symbol (format "x~a" (n-sub i))))))
            (define/contract b-𝒾s (listof identifier?) (map (curry datum->syntax f) b-syms))
            (define b-pats (for/list ([b-𝒾 b-𝒾s]) #`(-b #,b-𝒾)))
            (define b-conds (datum->syntax f (sexp-and (map mk-cond b-syms cs))))

            (list
             #`[(#,o)
                (match #,xs
                  [(list #,@b-pats) #:when #,b-conds (-b (#,o #,@b-𝒾s))]
                  #,@(cond
                       [(hash-ref prims:left-ids o #f) =>
                        (λ (lid) (list #`[(list (-b #,lid) e) e]))]
                       [else '()])
                  #,@(cond
                       [(hash-ref prims:right-ids o #f) =>
                        (λ (rid) (list #`[(list e (-b #,rid)) e]))]
                       [else '()])
                  #,@(cond
                       [(∋ prims:assocs o)
                        (list #`[(list (-@ '#,o (list e₁ e₂) _) e₃)
                                 (-@/simp '#,o e₁ (-@/simp '#,o e₂ e₃))])]
                       [else '()])
                  [_ #,default-case])])]
           [else '()])]
        [_ '()]))
    
    (define ans (append-map go prims:prims))
    ;(printf "~a~n" (pretty (map syntax->datum ans)))
    ans))

(: -@/simp : -e -e * → -e)
;; Smart constructor for application
(define (-@/simp f . xs)

  (: access-same-value? : -struct-info (Listof -e) → (Option -e))
  ;; If given expression list of the form like `(car e); (cdr e)`, return `e`.
  ;; Otherwise just `#f`
  (define (access-same-value? info es)
    (define n (-struct-info-arity info))
    (match es
      [(cons (-@ (-st-ac info₀ 0) (list e₀) _) es*)
       (and (equal? info info₀)
            (for/and : Boolean ([i (in-range 1 n)] [ei es*])
              (match ei
                [(-@ (-st-ac infoⱼ j) (list eⱼ) _)
                 (and (equal? info infoⱼ) (= i j) (equal? e₀ eⱼ))]
                [_ #f]))
            e₀)]
      [_ #f]))

  (define (default-case) : -e
    (-@ (assert f) (cast xs (Listof -e)) 0))

  (define-syntax (general-primitive-case stx)
    #`(case f
        #,@(general-primitive-clauses #'f #'xs)
        [else (default-case)]))

  (match f
    ['any/c -tt]
    ['none/c -ff]
    ['void (-b (void))]
    ['values
     (match xs
       [(list x) x]
       [_ (default-case)])]

    ; vector-length
    ['vector-length
     (match xs
       [(list (-@ 'vector xs _)) (-b (length xs))]
       [_ (default-case)])]

    ; (not³ e) = (not e) 
    ['not
     (match xs
       [(list (-@ 'not (and e* (-@ 'not _ _)) _)) e*]
       [(list (-@ 'not (-b x) _)) (-b (not (not x)))]
       [(list (-b x)) (-b (not x))]
       [_ (default-case)])]
    ['not/c
     (match xs
       [(list (-@ 'not/c (list (and e* (-@ 'not/c _ _))) _)) e*]
       [_ (default-case)])]
    [(-@ 'not/c (list f) _)
     (match xs
       [(list x) (-@/simp 'not (-@/simp f x))]
       [_ (default-case)])]

    ; TODO: handle `equal?` generally
    ['equal?
     (match xs
       [(list (-b b₁) (-b b₂)) (if (equal? b₁ b₂) -tt -ff)]
       [(list x x) -tt]
       [_ (default-case)])]

    ['defined?
      (match xs
        [(list (? -v?)) -tt]
        [_ (default-case)])]

    ['immutable?
     (match xs
       [(list (-@ 'vector _ _)) -ff]
       [_ (default-case)])]

    ; (car (cons e _)) = e
    [(-st-ac s i)
     (match xs
       [(list (-@ (-st-mk s) es _)) (list-ref es i)]
       [_ (default-case)])]
    [(-st-ac s i)
     (match-define (list x) xs)
     (cond ; don't build up syntax when reading from mutable states
       [(∋ (-struct-info-mutables s) i) #f]
       [else (-@ f (list (assert x)) 0)])]

    ; (cons (car e) (cdr e)) = e
    [(-st-mk s) (or (access-same-value? s xs) (-@ f xs 0))]

    ; General case
    [_ (general-primitive-case)]))
