#lang typed/racket/base

(provide
 FV 𝐴 closed? checks# count-xs free-x/c e/ e/map e/fun e/list find-calls prim-name->unsafe-prim)

(require
 racket/match racket/set racket/function
 "../utils/set.rkt" "../utils/untyped-macros.rkt" "definition.rkt")

(require/typed "../primitives/declarations.rkt"
  [prims (Listof Any)])
(require/typed racket/base
  [hash-empty? ((HashTable -e -e) → Boolean)])

(: FV : (U -e (Listof -e)) → (Setof Symbol))
;; Compute free variables for expression. Return set of variable names.
(define (FV e)
  (match e
    [(-x x) {set x}]
    [(-λ xs e)
     (define bound
       (match xs
         [(-varargs zs z) (set-add (list->set zs) z)]
         [(? list? xs) (list->set xs)]))
     (-- (FV e) bound)]
    [(-@ f xs _)
     (for/fold ([FVs (FV f)]) ([x xs]) (∪ FVs (FV x)))]
    [(-begin es) (FV es)]
    [(-begin0 e₀ es) (∪ (FV e₀) (FV es))]
    [(-let-values bnds e _)
     (define-values (bound FV_rhs)
       (for/fold ([bound : (Setof Symbol) ∅] [FV_rhs : (Setof Symbol) ∅]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ FV_rhs (FV rhs)))))
     (∪ FV_rhs (-- (FV e) bound))]
    [(-letrec-values bnds e _)
     (define bound
       (for/fold ([bound : (Setof Symbol) ∅]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     
     (for/fold ([xs : (Setof Symbol) (-- (FV e) bound)]) ([bnd bnds])
       (-- (FV (cdr bnd)) bound))]
    [(-set! x e) (set-add (FV e) x)]
    [(-@-havoc x) (FV x)]
    #;[(.apply f xs _) (set-union (FV f d) (FV xs d))]
    [(-if e e₁ e₂) (∪ (FV e) (FV e₁) (FV e₂))]
    [(-amb es)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e es])
       (∪ xs (FV e)))]
    [(-μ/c _ e) (FV e)]
    [(-->i doms rst rng _)
     (define-values (bound FV_dom)
       (for/fold ([bound : (Setof Symbol) ∅] [FV_dom : (Setof Symbol) ∅]) ([dom doms])
         (match-define (cons x c) dom)
         (values (set-add bound x) (∪ FV_dom (FV c)))))
     (∪ FV_dom
        (if rst (FV (cdr rst)) ∅)
        (-- (FV rng) (if rst (set-add bound (car rst)) bound)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (Setof Symbol) ∅]) ([c cs])
       (∪ xs (FV c)))]
    [(? list? l)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e l])
       (∪ xs (FV e)))]
    [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅]))

(module+ test
  (require typed/rackunit)
  
  (check-equal? (FV -tt) ∅)
  (check-equal? (FV (-λ '(x) (-x 'x))) ∅)
  (check-equal? (FV (-x 'x)) {set 'x})
  (check-equal? (FV (-ref (-id 'cons 'Λ) 'l 0)) ∅)
  (check-equal? (FV (-λ '(x) (-λ '(y) (-@ (-x 'f) (list (-x 'y) (-x 'x)) -Λ)))) {set 'f}))

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
    [(-->i doms rst rng _)
     (define-values (bound 𝐴_dom)
       (for/fold ([bound : (Setof Symbol) ∅] [𝐴_dom : (Setof Symbol) ∅]) ([dom doms])
         (match-define (cons x c) dom)
         (values (set-add bound x) (∪ 𝐴_dom (𝐴 c)))))
     (∪ 𝐴_dom
        (if rst (𝐴 (cdr rst)) ∅)
        (-- (𝐴 rng) (if rst (set-add bound (car rst)) bound)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (Setof Symbol) ∅]) ([c cs])
       (∪ xs (𝐴 c)))]
    [(? list? l)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e l])
       (∪ xs (𝐴 e)))]
    [_ (log-debug "𝐴⟦~a⟧ = ∅~n" e) ∅]))

(: closed? : -e → Boolean)
;; Check whether expression is closed
(define (closed? e) (set-empty? (FV e)))

(: checks# : (Rec X (U -top-level-form
                       -e
                       -general-top-level-form
                       -e
                       -module
                       -begin/top
                       -plain-module-begin
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
   [(-->i cs r d _)
    (+ (checks# ((inst map -e (Pairof Symbol -e)) cdr cs))
       (if r (checks# (cdr r)) 0)
       (checks# d))]
   [(-struct/c _ cs _) (checks# cs)]

   [(-plain-module-begin xs) (checks# xs)]
   [(-module _ body) (checks# body)]
   ;; FIXME count up for primitives
   [_ 0]))

(: count-xs : (U -e (Listof -e)) Symbol → Integer)
;; Count free occurences of variable with given name in expression(s)
(define (count-xs e x)
  (match e
    [(-x z) (if (equal? z x) 1 0)]
    [(-λ xs e) (if (binder-has? xs x) 0 (count-xs e x))]
    [(-case-λ clauses)
     (for/sum : Integer ([clause clauses])
       (match-define (cons xs e) clause)
       (if (binder-has? xs x) 0 (count-xs e x)))]
    [(-@ f xs _) (+ (count-xs f x) (count-xs xs x))]
    [(-if e e₁ e₂) (+ (count-xs e x) (count-xs e₁ x) (count-xs e₂ x))]
    [(-wcm k v b) (+ (count-xs k x) (count-xs v x) (count-xs b x))]
    [(-begin es) (count-xs es x)]
    [(-let-values bnds body _)
     (define-values (bound k)
       (for/fold ([bound : (Setof Symbol) ∅] [k : Integer 0]) ([bnd bnds])
         (match-define (cons xs e) bnd)
         (values (set-add-list bound xs) (+ k (count-xs e x)))))
     (+ k (if (set-member? bound x) 0 (count-xs body x)))]
    [(-letrec-values bnds body _)
     (define bound
       (for/fold ([bound : (Setof Symbol) ∅]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     (cond
       [(set-member? bound x) 0]
       [else
        (+ (for/sum : Integer ([bnd bnds])
             (count-xs (cdr bnd) x))
           (count-xs body x))])]
    [(-@-havoc (-x z)) (if (equal? z x) 1 0)]
    [(-amb es) (for/sum : Integer ([e es]) (count-xs e x))]
    [(-μ/c _ c) (count-xs c x)]
    [(-->i doms rst rng _)
     (define-values (bound k)
       (for/fold ([bound : (Setof Symbol) (if rst (set (car rst)) ∅)]
                  [k : Integer (if rst (count-xs (cdr rst) x) 0)])
                 ([dom doms])
         (match-define (cons z c) dom)
         (values (set-add bound z) (+ k (count-xs c x)))))
     (+ k (if (set-member? bound x) 0 (count-xs rng x)))]
    [(-struct/c _ cs _) (count-xs cs x)]
    [(? list? l) (for/sum : Integer ([i l]) (count-xs i x))]
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
      [(-->i cs rst d _)
       (∪ (go* ((inst map -e (Pairof Symbol -e)) cdr cs))
          (if rst (go (cdr rst)) ∅)
          (go d))]
      [(-struct/c t cs _) (go* cs)]
      [(-x/c.tmp x) (set x)]
      [_ ∅]))
  
  (go e))

(: e/ : -e -e -e → -e)
;; Substitution, where `x` can be an (open) term rather than just a free variable.
(define (e/ x eₓ e)
  ((e/map (hash e eₓ)) e))

(: e/list : (Listof -e) (Listof -e) -e → -e)
;; Simultaneous subtitution
(define (e/list xs exs e)
  (define m
    (for/hash : (HashTable -e -e) ([x xs] [ex exs])
      (values x ex)))
  ((e/map m) e))

(: e/map : (HashTable -e -e) → (-e → -e))
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
         [(-amb es) (-amb (for/set: : -es ([ei es]) (go m ei)))]
         [(-μ/c z c) (-μ/c z (go m c))]
         [(-->i doms rst rng p)
          (define-values (xs cs)
            (for/lists ([xs : (Listof Symbol)] [cs : (Listof -e)])
                       ([dom doms])
              (values (car dom) (go m (cdr dom)))))
          (define rng* (go (shrink m (if rst (cons (car rst) xs) xs)) rng))
          (-->i (map (inst cons Symbol -e) xs cs)
                (and rst (cons (car rst) (go m (cdr rst))))
                rng*
                p)]
         [(-struct/c t cs p) (-struct/c t (map (curry go m) cs) p)]
         [_
          (log-debug "e/: ignore substituting ~a" e)
          e])])))

(: e/fun : (-e → (Option -e)) → (-e → -e))
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
         [(-amb es) (-amb (for/set: : -es ([ei es]) (go f ei)))]
         [(-μ/c z c) (-μ/c z (go f c))]
         [(-->i doms rst rng p)
          (define-values (xs cs)
            (for/lists ([xs : (Listof Symbol)] [cs : (Listof -e)])
                       ([dom doms])
              (values (car dom) (go f (cdr dom)))))
          (define rng* (go (shrink-f f (if rst (cons (car rst) xs) xs)) rng))
          (-->i (map (inst cons Symbol -e) xs cs)
                (and rst (cons (car rst) (go f (cdr rst))))
                rng*
                p)]
         [(-struct/c t cs p) (-struct/c t (map (curry go f) cs) p)]
         [_
          (log-debug "e/: ignore substituting ~a" e)
          e])])))

;; Shrink domain of `m` to not be included by `xs`
(define (shrink [m : (HashTable -e -e)] [xs : -formals]) : (HashTable -e -e)
  (for/fold ([m* : (HashTable -e -e) m])
            ([x (in-hash-keys m)] #:when (binder-has? xs x))
    (cond [(-x? x) (hash-remove m* x)]
          [else (error 'e/m "unexpected")])))

(define (shrink-f [f : (-e → (Option -e))] [xs : -formals]) : (-e → (Option -e))
  (define shadows
    (match xs
      [(-varargs zs z) (set-add (list->set zs) z)]
      [(? list?) (list->set xs)]))
  (λ (e) (and (set-empty? (∩ shadows (FV e))) (f e))))

(: find-calls : -e -id → (Setof (Listof -e)))
;; Search for all invocations of `f-id` in `e`
(define (find-calls e f-id)
  (define-set calls : (Listof -e))
  (let go : Void ([e e])
       (match e
         [(-@ f xs _)
          (go f)
          (for-each go xs)
          (when (match? f (-ref (≡ f-id) _ _))
            (calls-add! xs))]
         [_ (void)]))
  calls)

(: binder-has? : -formals (U Symbol -e) → (Option (Setof Symbol)))
;; returns whether a list of binding names has given name
(define (binder-has? xs x)
  (define FVs (if (symbol? x) {set x} (FV x)))
  (define binders
    (match xs
      [(? list? xs) (list->set xs)]
      [(-varargs zs z) (set-add (list->set zs) z)]))
  (define captured (∩ FVs binders))
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
