#lang typed/racket/base

(provide
 fv 𝐴 closed? checks# free-x/c unroll find-calls prim-name->unsafe-prim
 α-rename e-map-union -@/simp
 -φ e->φ φ->e e/map φ/map e/ show-φ show-?φ fv-φ -φ -?φ m∅
 -⦇ff⦈ -⦇values⦈ -⦇fc⦈)

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
  [hash-empty? (Any #|hack|# → Boolean)])

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
  (check-equal? (fv (-λ '(x) (-λ '(y) (-@ (-x 'f) (list (-x 'y) (-x 'x)) 0)))) {set 'f}))

(: 𝐴 : (U -e (Listof -e)) → (℘ Var-Name))
;; Collect all asignable free variables
(define (𝐴 e)
  (match e
    [(-x x) ∅eq]
    [(-λ xs e)
     (define bound
       (match xs
         [(-varargs zs z) (set-add (list->seteq zs) z)]
         [(? list? xs) (list->seteq xs)]))
     (-- (𝐴 e) bound)]
    [(-@ f xs _)
     (for/fold ([𝐴s (𝐴 f)]) ([x xs]) (∪ 𝐴s (𝐴 x)))]
    [(-begin es) (𝐴 es)]
    [(-begin0 e₀ es) (∪ (𝐴 e₀) (𝐴 es))]
    [(-let-values bnds e)
     (define-values (bound 𝐴_rhs)
       (for/fold ([bound : (℘ Var-Name) ∅eq] [𝐴_rhs : (℘ Var-Name) ∅eq]) ([bnd bnds])
         (match-define (cons xs rhs) bnd)
         (values (set-add-list bound xs) (∪ 𝐴_rhs (𝐴 rhs)))))
     (∪ 𝐴_rhs (-- (𝐴 e) bound))]
    [(-letrec-values bnds e)
     (define bound
       (for/fold ([bound : (℘ Var-Name) ∅eq]) ([bnd bnds])
         (set-add-list bound (car bnd))))
     (for/fold ([xs : (℘ Var-Name) (-- (𝐴 e) bound)]) ([bnd bnds])
       (-- (𝐴 (cdr bnd)) bound))]
    [(-set! x e) (set-add (𝐴 e) x)]
    #;[(.apply f xs _) (set-union (𝐴 f d) (𝐴 xs d))]
    [(-if e e₁ e₂) (∪ (𝐴 e) (𝐴 e₁) (𝐴 e₂))]
    [(-amb es)
     (for/fold ([xs : (℘ Var-Name) ∅eq]) ([e es])
       (∪ xs (𝐴 e)))]
    [(-μ/c _ e) (𝐴 e)]
    [(--> cs d _) (apply ∪ (fv d) (map fv cs))]
    [(-->i cs mk-d _) (apply ∪ (𝐴 mk-d) (map 𝐴 cs))]
    [(-case-> clauses _)
     (for/unioneq : (℘ Var-Name) ([clause clauses])
       (match-define (cons cs d) clause)
       (apply ∪ (𝐴 d) (map 𝐴 cs)))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (℘ Var-Name) ∅eq]) ([c cs])
       (∪ xs (𝐴 c)))]
    [(? list? l)
     (for/fold ([xs : (℘ Var-Name) ∅eq]) ([e l])
       (∪ xs (𝐴 e)))]
    [_ (log-debug "𝐴⟦~a⟧ = ∅~n" e) ∅eq]))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Substitution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compiled symbol ready for substitution
(define-type -φ ((HashTable -φ -φ) → -e))
(define-type -?φ (Option -φ))
(define m∅ : (HashTable -φ -φ) (hasheq))

(: fv-φ : -?φ → (℘ Var-Name))
(define (fv-φ φ) (if φ (fv (φ->e φ)) ∅eq))

(define/memo (e->φ [e : -e]) : -φ

  (define-syntax-rule (with-m (m) body ...)
    (let ([memo : (HashTable (HashTable -φ -φ) -e) (make-hash)])
      (letrec ([φ : -φ (λ (m)
                         (cond [(hash-empty? m) e]
                               [(hash-ref m φ #f) => φ->e]
                               [else (hash-ref! memo m (λ () body ...))]))])
        φ)))

  (match e
    [_ #:when (set-empty? (fv e))
     (log-debug "⦇e⦈: optimize for closed term ~a~n" (show-e e))
     (letrec ([φ : -φ (λ (m)
                        (cond [(hash-ref m φ #f) => φ->e]
                              [else e]))])
       φ)]
    [(-λ xs e*)
     (define ⦇e*⦈ (e->φ e*))
     (define fvs (formals->names xs))
     (with-m (m)
       (-λ xs (⦇e*⦈ (shrink m fvs))))]
    [(-case-λ clauses)
     (define-values (xss fvss ⦇e⦈s)
       (for/lists ([xss  : (Listof (Listof Var-Name))]
                   [fvss : (Listof (℘ Var-Name))]
                   [⦇e⦈s  : (Listof -φ)])
                  ([clause clauses])
         (match-define (cons xs eₓ) clause)
         (values xs (list->seteq xs) (e->φ eₓ))))
     (with-m (m)
       (-case-λ
        (for/list : (Listof (Pairof (Listof Var-Name) -e)) ([xs xss] [fvs fvss] [⦇e⦈ ⦇e⦈s])
          (cons xs (⦇e⦈ (shrink m fvs))))))]
    [(-@ f xs _)
     (define ⦇f⦈ (e->φ f))
     (define ⦇x⦈s (map e->φ xs))
     (with-m (m)
       (apply -@/simp (⦇f⦈ m) (for/list : (Listof -e) ([⦇x⦈ ⦇x⦈s]) (⦇x⦈ m))))]
    [(-if e₀ e₁ e₂)
     (define ⦇e₀⦈ (e->φ e₀))
     (define ⦇e₁⦈ (e->φ e₁))
     (define ⦇e₂⦈ (e->φ e₂))
     (with-m (m)
       (-if (⦇e₀⦈ m) (⦇e₁⦈ m) (⦇e₂⦈ m)))]
    [(-wcm k v b)
     (define ⦇k⦈ (e->φ k))
     (define ⦇v⦈ (e->φ v))
     (define ⦇b⦈ (e->φ b))
     (with-m (m)
       (-wcm (⦇k⦈ m) (⦇v⦈ m) (⦇b⦈ m)))]
    [(-begin es)
     (define ⦇e⦈s (map e->φ es))
     (with-m (m)
       (-begin (for/list : (Listof -e) ([⦇e⦈ ⦇e⦈s]) (⦇e⦈ m))))]
    [(-begin0 e₀ es)
     (define ⦇e₀⦈ (e->φ e₀))
     (define ⦇e⦈s (map e->φ es))
     (with-m (m)
       (-begin0 (⦇e₀⦈ m) (for/list ([⦇e⦈ ⦇e⦈s]) (⦇e⦈ m))))]
    [(-let-values bnds e*)
     (define-values (formals-rev locals ⦇e⦈s-rev)
       (for/fold ([formals-rev : (Listof (Listof Var-Name)) '()]
                  [locals : (℘ Var-Name) ∅eq]
                  [⦇e⦈s-rev : (Listof -φ) '()])
                 ([bnd bnds])
         (match-define (cons xs eₓ) bnd)
         (values (cons xs formals-rev)
                 (set-add-list locals xs)
                 (cons (e->φ eₓ) ⦇e⦈s-rev))))
     (define ⦇e*⦈ (e->φ e*))
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
                  [locals : (℘ Var-Name) ∅eq]
                  [⦇e⦈s-rev : (Listof -φ) '()])
                 ([bnd bnds])
         (match-define (cons xs eₓ) bnd)
         (values (cons xs formals-rev)
                 (set-add-list locals xs)
                 (cons (e->φ eₓ) ⦇e⦈s-rev))))
     (define ⦇e*⦈ (e->φ e*))
     (with-m (m)
       (define m* (shrink m locals))
       (define bnds*
         (for/fold ([acc : (Listof (Pairof (Listof Var-Name) -e)) '()])
                   ([xs (in-list formals-rev)]
                    [⦇e⦈ (in-list ⦇e⦈s-rev)])
           (cons (cons xs (⦇e⦈ m*)) acc)))
       (-letrec-values bnds* (⦇e*⦈ m*)))]
    [(-set! x e*)
     (define ⦇e*⦈ (e->φ e*))
     (with-m (m) (-set! x (⦇e*⦈ m)))]
    [(-amb es)
     (define ⦇e⦈s : (Listof -φ) (for/list ([e es]) (e->φ e)))
     (with-m (m)
       (-amb (for/set: : (℘ -e) ([⦇e⦈ ⦇e⦈s]) (⦇e⦈ m))))]
    [(-μ/c z c)
     (define ⦇c⦈ (e->φ c))
     (with-m (m) (-μ/c z (⦇c⦈ m)))]
    [(--> cs d ℓ)
     (define ⦇c⦈s (map e->φ cs))
     (define ⦇d⦈ (e->φ d))
     (with-m (m)
       (--> (for/list ([⦇c⦈ ⦇c⦈s]) (⦇c⦈ m)) (⦇d⦈ m) ℓ))]
    [(-->i cs mk-d ℓ)
     (define ⦇c⦈s (map e->φ cs))
     (define ⦇mk-d⦈ (e->φ mk-d))
     (with-m (m)
       (-->i (for/list ([⦇c⦈ ⦇c⦈s]) (⦇c⦈ m)) (assert (⦇mk-d⦈ m) -λ?) ℓ))]
    [(-case-> clauses ℓ)
     (define ⦇clause⦈s : (Listof (Pairof (Listof -φ) -φ))
       (for/list ([clause clauses])
         (match-define (cons doms rng) clause)
         (cons (map e->φ doms) (e->φ rng))))
     (with-m (m)
       (-case->
        (for/list : (Listof (Pairof (Listof -e) -e)) ([⦇clause⦈ ⦇clause⦈s])
          (match-define (cons ⦇dom⦈s ⦇rng⦈) ⦇clause⦈)
          (cons (for/list : (Listof -e) ([⦇dom⦈ ⦇dom⦈s]) (⦇dom⦈ m))
                (⦇rng⦈ m)))
        ℓ))]
    [(-struct/c t cs ℓ)
     (define ⦇c⦈s (map e->φ cs))
     (with-m (m)
       (-struct/c t (for/list ([⦇c⦈ ⦇c⦈s]) (⦇c⦈ m)) ℓ))]
    [_
     (log-debug "e->φ: constant ~a" (show-e e))
     (letrec ([φ : -φ (λ (m)
                        (cond
                          [(hash-ref m φ #f) => φ->e]
                          [else e]))])
       φ)]))

(define (φ/map [m : (HashTable -φ -φ)] [φ : -φ]) (e->φ (φ m)))
(define (φ->e [φ : -φ]) (φ m∅))
(define (e/map [m : (HashTable -φ -φ)] [e : -e]) ((e->φ e) m))

(: e/ : -e -e -e → -e)
;; Substitution, where `x` can be an (open) term rather than just a free variable.
(define (e/ x eₓ e) (e/map (hasheq (e->φ x) (e->φ eₓ)) e))

(: shrink : (HashTable -φ -φ) (℘ Var-Name) → (HashTable -φ -φ))
(define (shrink m xs)
  (for/fold ([m* : (HashTable -φ -φ) m])
            ([φₓ (in-hash-keys m)]
             #:unless (set-empty? (∩ xs (fv-φ φₓ))))
    (hash-remove m* φₓ)))

(: formals->names : -formals → (℘ Var-Name))
(define (formals->names xs)
  (cond
    [(-varargs? xs) (set-add (list->seteq (-varargs-init xs)) (-varargs-rest xs))]
    [else (list->seteq xs)]))

(: e-map-union : (HashTable -φ -φ) (HashTable -φ -φ) → (HashTable -φ -φ))
(define (e-map-union m δm)
  (for/fold ([m : (HashTable -φ -φ) m])
            ([(x y) δm])
    (cond
      [(hash-ref m x #f) =>
       (λ (y*)
         (unless (equal? y* y)
           (log-warning "e-map-union: ~a ↦ ~a, updated to ~a~n" (show-φ x) (show-φ y*) (show-φ y))))])
    (hash-set m x y)))

(define (show-φ [φ : -φ]) (show-e (φ->e φ)))
(define (show-?φ [φ : -?φ]) (if φ (show-e (φ->e φ)) '∅))

(define -⦇ff⦈ (e->φ -ff))
(define -⦇values⦈ (e->φ 'values))
(define -⦇fc⦈ (e->φ 'fc))
