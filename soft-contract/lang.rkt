#lang typed/racket
(require racket/splicing "utils.rkt"
         (for-syntax racket/base racket/syntax))
(require/typed redex/reduction-semantics
  [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;; I prefix types with dashes so I can use 1-letter variables without shadowing constructors

(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

(define-type/pred Adhoc-Module-Path (U Symbol String) #|TODO|#)
(define-type Mon-Party Adhoc-Module-Path)
(define-type Mon-Info (List Mon-Party Mon-Party Mon-Party))
(struct -src-loc ([party : Mon-Party] [loc : (Option Integer)]) #:transparent)
(struct -id ([name : Symbol] [ctx : Adhoc-Module-Path]) #:transparent)

(define -Λ (-src-loc 'Λ #f))

(: swap-parties : Mon-Info → Mon-Info)
;; Swap positive and negative blame parties
(define/match (swap-parties info)
  [((list + - o)) (list - + o)])

(: -begin/simp : (∀ (X) (Listof X) → (U X (-begin X))))
;; Smart constructor for begin, simplifying single-eession case
(define/match (-begin/simp xs)
  [((list e)) e]
  [(es) (-begin es)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type/pred Base
  (U Number Boolean String Symbol Keyword #|Sexp Bytes Regexp PRegexp|#))

(define-data -top-level-form
  -general-top-level-form
  -e
  -module
  -begin/top)

(define-data -module-level-form
  -general-top-level-form
  (struct -provide [specs : (Listof -provide-spec)])
  -submodule-form)

(define-data -general-top-level-form
  -e
  (struct -define-values [ids : (Listof Symbol)] [e : -e])
  (struct -require [specs : (Listof -require-spec)]))

(define-data -submodule-form
  (struct -module [path : Adhoc-Module-Path] [body : -plain-module-begin]))

(define-data -provide-spec
  (struct -p/c-item [id : Symbol] [spec : -e] #|TODO|#))

(define-data -require-spec
  Adhoc-Module-Path #|TODO|#)

(struct -plain-module-begin ([body : (Listof -module-level-form)]) #:transparent)

(define-data -e
  (subset: -v
    (struct -λ [formals : -formals] [body : -e])
    (struct -case-λ [body : (Listof (Pairof -formals -e))])
    (subset: -•
      '•
      ;; `l` is a tag annotating which static location this opaque value came from
      (struct -•ₗ [l : Natural]))
    (subset: -prim
      ;; primitive values that can appear in syntax
      (struct -b [unboxed : Base])
      (subset: -o
        'values
        (subset: -o1
          (subset: -pred
            ;; `arity` is the number of fields in the struct
            (struct -st-p [tag : -id] [arity : Integer])
            'defined?
            'number? 'real? 'integer? 'not 'boolean? 'string? 'symbol? 'procedure? 'keyword?
            'vector?)
          ;; `arity` is the number of fields in the struct
          ;; `index` is the index that this accesses
          (struct -st-ac [tag : -id] [arity : Integer] [index : Integer])
          'add1 'sub1 'string-length 'sqrt
          'sin 'cos 'tan 'abs 'round 'floor 'ceiling 'log
          'vector-length
          ;; temporary ops
          'sqr
          )
        (subset: -o2
          'equal? '= '> '< '>= '<= '+ '- '* '/
          'expt 'abs 'min 'max
          'arity=? 'arity>=? 'arity-includes?
          'remainder 'quotient
          'vector-ref
          (struct -st-mut [tag : -id] [arity : Integer] [index : Integer]))
        (struct -st-mk [tag : -id] [arity : Integer])
        'vector 'vector-set!)))
  ;; lexical variables
  (struct -x [name : Symbol])
  ;; module references
  (struct -ref [id : -id] [ctx : Mon-Party])
  (struct -@ [f : -e] [xs : (Listof -e)] [loc : -src-loc])
  (struct -if [i : -e] [t : -e] [e : -e])
  (struct -wcm [key : -e] [val : -e] [body : -e])
  -begin/e
  (struct -begin0 [e0 : -e] [es : (Listof -e)])
  (struct -quote [v : Any])
  (struct -let-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e] [ctx : Mon-Party])
  (struct -letrec-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e] [ctx : Mon-Party])
  (struct -set! [x : Symbol] [e : -e])

  (struct -@-havoc [x : -x]) ; hack for havoc to detect argument's arity at runtime
  (struct -amb [es : -es])
  
  ;; contract stuff
  (struct -μ/c [x : Symbol] [c : -e] [pos : (Option Integer)])
  (struct -->i [dom : (Listof (Pairof Symbol -e))] [rng : -e] [pos : (Option Integer)])
  (struct -x/c [x : Symbol])
  (struct -struct/c [tag : -id] [fields : (Listof -e)] [pos : (Option Integer)])
  #;(-and/c [l : .e] [r : .e])
  #;(-or/c [l : .e] [r : .e])
  #;(.¬/c [c : .e]))

(define-type -es (Setof -e))

(: -formal-names : -formals → (Setof Symbol))
;; Return all variable names in function's parameter list
(define -formal-names
  (match-lambda
    [(? list? xs) (list->set xs)]
    [(-varargs xs x) (set-add (list->set xs) x)]))

;; frequently used constants
(define -tt (-b #t))
(define -ff (-b #f))
(define -any/c (-λ '(x) -tt))
(define -none/c (-λ '(x) -ff))
(define -null/c (-st-p (-id 'null 'Λ) 0))
(define -cons (-st-mk (-id 'cons 'Λ) 2))
(define -car (-st-ac (-id 'cons 'Λ) 2 0))
(define -cdr (-st-ac (-id 'cons 'Λ) 2 1))
(define -cons? (-st-p (-id 'cons 'Λ) 2))
(define -zero (-b 0))
(define -one (-b 1))
(define -void #|hack|# (-@ (-st-mk (-id 'void 'Λ) 0) '() -Λ))
(define -null? (-st-p (-id 'null 'Λ) 0))
(define -null #|hack|# (-@ (-st-mk (-id 'null 'Λ) 0) '() -Λ))
(define -box? (-st-p (-id 'box 'Λ) 1))
(define -unbox (-st-ac (-id 'box 'Λ) 1 0))
(define -box (-st-mk (-id 'box 'Λ) 1))
(define -set-box! (-st-mut (-id 'box 'Λ) 1 0))

(: --> : (Listof -e) -e (Option Integer) → -e)
;; Make a non-dependent contract as a special case of dependent contract
(define (--> cs d pos)
  (define doms
    (for/list : (Listof (Pairof Symbol -e)) ([c cs] [i (in-naturals)])
      (define x (string->symbol (format "x•~a" (n-sub i)))) ; hack
      (cons x c)))
  (-->i doms d pos))

;; Current restricted representation of program
(struct -prog ([modules : (Listof -module)] [main : -e]) #:transparent)

(define-data -formals
  (Listof Symbol)
  (struct -varargs [init : (Listof Symbol)] [rest : Symbol]))

(: •! : → -•ₗ)
;; Generate new labeled hole
(define •!
  (let ([n : Natural 0])
    (λ () (begin0 (-•ₗ n) (set! n (+ 1 n))))))

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
    [(-μ/c x e _) (set-remove (FV e) x)]
    [(-->i doms rng _)
     (define-values (bound FV_dom)
       (for/fold ([bound : (Setof Symbol) ∅] [FV_dom : (Setof Symbol) ∅]) ([dom doms])
         (match-define (cons x c) dom)
         (values (set-add bound x) (∪ FV_dom (FV c)))))
     (∪ FV_dom (-- (FV rng) bound))]
    [(-struct/c _ cs _)
     (for/fold ([xs : (Setof Symbol) ∅]) ([c cs])
       (∪ xs (FV c)))]
    [(? list? l)
     (for/fold ([xs : (Setof Symbol) ∅]) ([e l])
       (∪ xs (FV e)))]
    [_ (log-debug "FV⟦~a⟧ = ∅~n" e) ∅]))

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
   [(-define-values _ e) (checks# e)]
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
   [(-μ/c _ c _) (checks# c)]
   [(-->i cs d _) (+ (checks# ((inst map -e (Pairof Symbol -e)) cdr cs)) (checks# d))]
   [(-struct/c _ cs _) (checks# cs)]

   [(-plain-module-begin xs) (checks# xs)]
   [(-module _ body) (checks# body)]
   [(or (? -pred?) (? -st-mk?)) 0]
   [(? -o1?) 1]
   [(? -o2?) 2]
   [_ 0]))

(splicing-let ([mk-and/c (-st-mk (-id 'and/c 'Λ) 2)]
               [mk-or/c (-st-mk (-id 'or/c 'Λ) 2)]
               [mk-cons/c (-st-mk (-id 'cons/c 'Λ) 2)]
               [mk-not/c (-st-mk (-id 'not/c 'Λ) 1)])
  (:* -and/c -or/c -one-of/c : (Pairof -e (Option Integer)) * → -e)
  (define -and/c
    (match-lambda*
      [(list) -any/c]
      [(list (cons c _)) c]
      [(cons (cons c p) cs)
       (-@ mk-and/c (list c (apply -and/c cs)) (-src-loc 'Λ p))]))
  (define -or/c
    (match-lambda*
      [(list) -none/c]
      [(list (cons c _)) c]
      [(cons (cons c p) cs)
       (-@ mk-or/c (list c (apply -or/c cs)) (-src-loc 'Λ p))]))
  (define -one-of/c
    (match-lambda*
      [(list) -none/c]
      [(list (cons e _)) (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) -Λ))]
      [(cons (cons e p) es)
       (-or/c (cons (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) -Λ)) p)
              (cons (apply -one-of/c es) #f))]))
  
  (: -cons/c : -e -e (Option Integer) → -e)
  (define (-cons/c c d pos) (-struct/c (-id 'cons 'Λ) (list c d) pos))

  (: -not/c : -e (Option Integer) → -e)
  (define (-not/c c pos) (-@ (-st-mk (-id 'not/c 'Λ) 1) (list c) (-src-loc 'Λ pos))))

(: -list/c : (Pairof -e (Option Integer)) * → -e)
(define (-list/c . cs)
  (match cs
    ['() -null/c]
    [(cons (cons c p) cs*)
     (-cons/c c (apply -list/c cs*) p)]))

(: -list : (Pairof -e -src-loc) * → -e)
(define (-list . es)
  (match es
    ['() -null]
    [(cons (cons e loc) es*)
     (-@ -cons (list e (apply -list es*)) loc)]))

;; Macros
(:* -and : -e * → -e)
;; Return ast representing conjuction of 2 expressions
(define -and
  (match-lambda*
    [(list) -tt]
    [(list e) e]
    [(cons e es) (-if e (apply -and es) -ff)]))

(: -comp/c : -o2 -e → -e)
;; Return ast representing `(op _ e)`
(define (-comp/c op e)
  (define x (variable-not-in (set->list (FV e)) 'x₀))
  (-λ (list x) (-and (-@ 'real? (list (-x x)) -Λ) (-@ op (list (-x x) e) -Λ))))


(define -havoc-path 'havoc)
(define -havoc-id (-id 'havoc-id -havoc-path)) ; havoc function id
(define -havoc-src (-src-loc -havoc-path #f)) ; havoc module path

(define (havoc-ref-from [ctx : Mon-Party])
  (-ref -havoc-id ctx))

(: prog-accs : (Listof -module) → (Setof -st-ac))
;; Retrieve set of all public accessors from program
(define (prog-accs ms)
  ;; FIXME: generate accessors properly
  {set})

(: gen-havoc : (Listof -module) → (Values -module -e))
;; Generate:
;; - havoc module
;; - expression havoc-ing exported identifiers from all concrete modules
(define (gen-havoc ms)

  ;;; Generate module
  (define havoc-ref (havoc-ref-from -havoc-path))
  (define x (-x '☠))
  (define havoc-func ; only used by `verify` module, not `ce`
    (-λ (list '☠)
        (-amb/simp
         (cons (-@ havoc-ref (list (-@-havoc x)) -havoc-src)
               (for/list : (Listof -@) ([ac (prog-accs ms)])
                 (-@ havoc-ref (list (-@ ac (list x) -havoc-src)) -havoc-src))))))
  (define m
    (-module -havoc-path
             (-plain-module-begin
              (list
               (-define-values (list (-id-name -havoc-id)) havoc-func)
               (-provide (list (-p/c-item (-id-name -havoc-id) -any/c)))))))

  ;;; Generate expression
  (define-set refs : -ref)
  #;(log-debug "~nmodules: ~n~a~n" ms)
  (for ([m (in-list ms)])
    (cond
      [(module-opaque? m)
       =>
       (λ (s)
         (log-debug "Omit havocking opaque module `~a`. Provided but undefined: ~a~n"
                   (-module-path m)
                   (set->list s)))]
     [else
      #;(log-debug "Havocking transparent module ~a~n" (-module-path m))
      (match-define (-module path (-plain-module-begin forms)) m)
      #;(eprintf "Insert exported identifiers from module ~a to unknown contexts~n" path)
      (for* ([form (in-list forms)]
             #:when (-provide? form)
             [spec (in-list (-provide-specs form))])
        (log-debug "adding: ~a~n" (-p/c-item-id spec))
        (refs-add! (-ref (-id (-p/c-item-id spec) path) '†)))]))
  #;(log-debug "~nrefs: ~a~n" refs)
  (define expr
    (-amb/remember (for/list ([ref (in-set refs)])
                     (-@ (•!) (list ref) -havoc-src))))

  #;(log-debug "~nhavoc-e:~n~a" expr)

  (values m expr))

(: -amb/simp : (Listof -e) → -e)
;; Smart constructor for `amb` with simplification for 1-expression case
(define -amb/simp
  (match-lambda
    [(list e) e]
    [es (-amb (list->set es))]))

(: -amb/remember : (Listof -e) → -e)
;; Return ast representing "remembered" non-determinism
(define/match (-amb/remember es)
  [((list)) -ff]
  [((list e)) e]
  [((cons e es)) (-if (•!) e (-amb/remember es))])

(: module-opaque? : -module → (U #f (Setof Symbol)))
;; Check whether module is opaque, returning the set of opaque exports if so
(define (module-opaque? m)
  (match-define (-module _ (-plain-module-begin body)) m)
  
  (define-values (exports defines)
    (for/fold ([exports : (Setof Symbol) ∅] [defines : (Setof Symbol) ∅])
              ([e (in-list body)])
      (match e
        [(-provide specs)
         (values (set-add-list exports (map -p/c-item-id specs)) defines)]
        [(-define-values xs _)
         (values exports (set-add-list defines xs))]
        [_ (values exports defines)])))

  (if (⊆ exports defines) #f (-- exports defines)))

(: binder-has? : -formals (U Symbol -e) → Boolean)
;; returns whether a list of binding names has given name
(define (binder-has? xs x)
  (define FVs (if (symbol? x) {set x} (FV x)))
  (define binders
    (match xs
      [(? list? xs) xs]
      [(-varargs zs z) (cons z zs)]))
  (not (set-empty? (∩ FVs (list->set binders)))))

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
    [(-μ/c z c _) (if (equal? z x) 0 (count-xs c x))]
    [(-->i doms rng _)
     (define-values (bound k)
       (for/fold ([bound : (Setof Symbol) ∅] [k : Integer 0]) ([dom doms])
         (match-define (cons z c) dom)
         (values (set-add bound z) (+ k (count-xs c x)))))
     (+ k (if (set-member? bound x) 0 (count-xs rng x)))]
    [(-struct/c _ cs _) (count-xs cs x)]
    [(? list? l) (for/sum : Integer ([i l]) (count-xs i x))]
    [_ 0]))

(: path->module ([(Listof -module) Adhoc-Module-Path] [(U Symbol False)] . ->* . -module))
;; Search for module at given path, given list of modules.
;; The optional `ref-name` parameter is merely a hack for a more informative error message.
(define (path->module ms x [ref-name #f])
  ;; - figure out module-path properly
  (or (for/or : (U #f -module) ([m (in-list ms)] #:when (equal? (-module-path m) x))
        m)
      (error 'path->module "Cannot find module `~a`~a" x
             (if ref-name (format " (when resolving `~a`)" ref-name) ""))))

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
      [(-μ/c z c _) (set-remove (go c) z)]
      [(-->i cs d _) (∪ (go* ((inst map -e (Pairof Symbol -e)) cdr cs)) (go d))]
      [(-struct/c t cs _) (go* cs)]
      [(-x/c x) (set x)]
      [_ ∅]))
  
  (go e))

(: id/c : -id → -id)
;; HACK
(define (id/c id)
  (match-define (-id name path) id)
  (-id (string->symbol (format "~a/c" name)) path))

(: e/ : -e (U Symbol -e) -e → -e)
;; Substitution
(define (e/ e x eₓ)

  (: guard : -formals → Void)
  (define guard
    (cond
      [(and (-e? x) (not (-x? x)))
       (λ (xs)
         (error 'e/ "variables in ~a captures ~a" xs (show-e e)))]
      [else (λ (_) (void))]))
  
  (let go ([e e])
    (match e
      [(? (curry equal? x)) eₓ]
      [(-λ xs e*)
       (cond [(binder-has? xs x) (guard xs) e]
             [else (-λ xs (go e*))])]
      [(-case-λ clauses)
       (-case-λ
        (for/list : (Listof (Pairof -formals -e)) ([clause clauses])
          (match-define (cons xs e*) clause)
          (cond [(binder-has? xs x) (guard xs) clause]
                [else (cons xs (go e*))])))]
      [(? -v?) e]
      [(-x z) (if (equal? x z) eₓ e)]
      [(? -ref?) e]
      [(-@ f xs l) (-@ (go f) (map go xs) l)]
      [(-if e₀ e₁ e₂) (-if (go e₀) (go e₁) (go e₂))]
      [(-wcm k v b) (-wcm (go k) (go v) (go b))]
      [(-begin0 e₀ es) (-begin0 (go e₀) (map go es))]
      [(? -quote?) e]
      [(-let-values bnds e* l)
       (define-values (bnds-rev locals)
         (for/fold ([bnds-rev : (Listof (Pairof (Listof Symbol) -e)) '()]
                    [locals : (Setof Symbol) ∅])
                   ([bnd bnds])
           (match-define (cons xs ex) bnd)
           (values (cons (cons xs (go ex)) bnds-rev)
                   (set-add-list locals xs))))
       (define bnds* (reverse bnds-rev))
       (define e**
         (cond [(∋ locals x) e*]
               [else (go e*)]))
       (-let-values bnds* e** l)]
      [(-letrec-values bnds e* l)
       (define locals
         (for/fold ([locals : (Setof Symbol) ∅]) ([bnd bnds])
           (set-add-list locals (car bnd))))
       (cond
         [(∋ locals x) e]
         [else
          (define bnds*
            (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
              (match-define (cons xs ex) bnd)
              (cons xs (go ex))))
          (-letrec-values bnds* (go e*) l)])]
      [(-set! z e*) (-set! z (go e*))]
      [(-amb es) (-amb (for/set: : -es ([ei es]) (go ei)))]
      [(-μ/c z c p) (-μ/c z (go c) p)]
      [(-->i doms rng p)
       (define-values (xs cs)
         (for/lists ([xs : (Listof Symbol)] [cs : (Listof -e)])
                    ([dom doms])
           (values (car dom) (go (cdr dom)))))
       (define rng*
         (cond [(member x xs) rng]
               [else (go rng)]))
       (-->i (map (inst cons Symbol -e) xs cs) rng* p)]
      [(-struct/c t cs p) (-struct/c t (map go cs) p)]
      [_
       (log-debug "e/: ignore substituting ~a" e)
       e])))

(: find-calls : -e -id → (Setof (Listof -e)))
;; Search for all invocations of `f-id` in `e`
(define (find-calls e f-id)
  (define-set calls : (Listof -e))
  (let go : Void ([e e])
       (match e
         [(-@ f xs _)
          (go f)
          (for-each go xs)
          (when (match? f (-ref (? (curry equal? f-id)) _))
            (calls-add! xs))]
         [_ (void)]))
  calls)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; PRETTY PRINTING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (show-src-loc [loc : -src-loc]) : Symbol
  (match-define (-src-loc lab pos) loc)
  (string->symbol (format "~a~a" lab (if pos (n-sub pos) ""))))

(define (show-b [x : Base]) : Sexp
  (cond
    [(string? x) (format "\"~a\"" x)]
    [(or (symbol? x) (keyword? x)) `(quote ,x)]
    [(and (real? x) (inexact? x))
     (define s (number->string x))
     (substring s 0 (min (string-length s) 5))]
    [else x]))

;; Return operator's simple show-o for pretty-printing
(define show-o : (-o → Symbol)
  (match-lambda
   [(? symbol? s) s]
   [(-st-mk (-id t _) _) t]
   [(-st-ac (-id 'cons 'Λ) 2 0) 'car]
   [(-st-ac (-id 'cons 'Λ) 2 1) 'cdr]
   [(-st-ac (-id 'box 'Λ) 1 0) 'unbox]
   [(-st-ac (-id t _) _ i) (string->symbol (format "~a@~a" t i))]
   [(-st-p (-id t _) _) (string->symbol (format "~a?" t))]))

(define (show-e [e : -e]) : Sexp
  (match e
    ; syntactic sugar
    [(-λ (list x) (-@ '= (list (-x x) e*) _)) `(=/c ,(show-e e*))]
    [(-λ (list x) (-@ 'equal? (list (-x x) e*) _)) `(≡/c ,(show-e e*))]
    [(-λ (list x) (-@ '> (list (-x x) e*) _)) `(>/c ,(show-e e*))]
    [(-λ (list x) (-@ '< (list (-x x) e*) _)) `(</c ,(show-e e*))]
    [(-λ (list x) (-@ '>= (list (-x x) e*) _)) `(≥/c ,(show-e e*))]
    [(-λ (list x) (-@ '<= (list (-x x) e*) _)) `(≤/c ,(show-e e*))]
    [(-λ (list x) (-@ (? closed? f) (list (-x x)) _)) (show-e f)]
    [(-λ (list x) (-@ 'arity-includes? (list (-x x) (-b 0)) _)) `(arity-includes/c ,x)]
    [(-λ (list x) (-@ 'arity=? (list (-x x) (-b 0)) _)) `(arity=/c ,x)]
    [(-λ (list x) (-@ 'arity>=? (list (-x x) (-b 0)) _)) `(arity≥/c ,x)]
    [(-λ (list _) (-b #t)) 'any/c]
    [(-λ (list _) (-b #f)) 'none/c]
    [(-@ (-st-mk (-id 'null 'Λ) 0) (list) _) 'null]
    [(-@ (-λ (list x) (-x x)) (list e) _) (show-e e)]
    [(-@ (-λ (list x) (-if (-x x) (-x x) b)) (list a) _)
     (match* ((show-e a) (show-e b))
       [(`(or ,l ...) `(or ,r ...)) `(or ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(or ,l ...) r) `(or ,@(cast l Sexps) ,r)]
       [(l `(or ,r ...)) `(or ,l ,@(cast r Sexps))]
       [(l r) `(or ,l ,r)])]
    [(-@ (-st-mk (-id (and n (or 'and/c 'or/c 'not/c)) 'Λ) _) c* _) `(,n ,@(show-es c*))]
    #| TODO obsolete? 
    [(-if (and e (-•ₗ α)) e₁ e₂)
    (match (σ@ σ α)
    [(-b #f) (go ctx e₂)]
    [(not '•) (go ctx e₁)]
    [_ `(if ,(go ctx e) ,(go ctx e₁) ,(go ctx e₂))])]
    |#
    [(-if a b (-b #f))
     (match* ((show-e a) (show-e b))
       [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(and ,l ...) r) `(and ,@(cast l Sexps) ,r)]
       [(l `(and ,r ...)) `(and ,l ,@(cast r Sexps))]
       [(l r) `(and ,l ,r)])]
    [(-if a b (-b #t)) `(implies ,(show-e a) ,(show-e b))]

    [(-λ (list xs ...) e) `(λ ,xs ,(show-e e))]
    [(-λ (-varargs xs rest) e) `(λ ,(cons xs rest) ,(show-e e))]
    [(-•ₗ n) (string->symbol (format "•~a" (n-sub n)))]
    [(-b b) (show-b b)]
    [(-st-mk t _) (-id-name t)]
    [(-st-ac (-id 'cons 'Λ) _ 0) 'car]
    [(-st-ac (-id 'cons 'Λ) _ 1) 'cdr]
    [(-st-ac t _ i) (string->symbol (format "~a@~a" (-id-name t) i))]
    [(-st-p t _) (string->symbol (format "~a?" (-id-name t)))]
    [(? -o? o) (show-o o)]
    [(-x x) x]
    [(-ref x _) (-id-name x)]
    [(-let-values bnds body _)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-letrec-values bnds body _)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-set! x e) `(set! ,x ,(show-e e))]
    [(-@ f xs _) `(,(show-e f) ,@(show-es xs))]
    [(-@-havoc x) `(havoc ,(show-e x))]
    [(-begin es) `(begin ,@(show-es es))]
    [(-begin0 e es) `(begin ,(show-e e) ,@(show-es es))]
    #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
    [(-if i t e) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
    [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (show-e e)))]
    [(-μ/c x c _) `(μ/c (,x) ,(show-e c))]
    [(-->i doms rng _) `(,@(for/list : (Listof Sexp) ([dom doms])
                           (match-define (cons x c) dom)
                           `(,x : ,(show-e c)))
                       ↦ ,(show-e rng))]
    [(-x/c x) x]
    [(-struct/c t cs _) `(,(string->symbol (format "~a/c" (-id-name t))) ,@(show-es cs))]))

(define (show-es [es : (Sequenceof -e)]) : (Listof Sexp)
  (for/list ([e es]) (show-e e)))
