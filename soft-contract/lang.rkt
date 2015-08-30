#lang typed/racket
(require racket/splicing "utils.rkt"
         (for-syntax racket/base racket/syntax))
(require/typed redex/reduction-semantics
  [variable-not-in (Any Symbol → Symbol)])
(provide (all-defined-out))

;; prefixing types with dashes so i can use 1-letter variables without shadowing constructors

(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

(define-type/pred Adhoc-Module-Path (U Symbol String) #|TODO|#)
(define-type Mon-Party Adhoc-Module-Path)
(define-type Mon-Info (List Mon-Party Mon-Party Mon-Party))

(: swap-parties : Mon-Info → Mon-Info)
;; Swap positive and negative blame parties
(define/match (swap-parties info)
  [((list + - o)) (list - + o)])

(: -begin/simp : (∀ (X) (Listof X) → (U X (-begin X))))
;; Smart constructor for begin, simplifying single-eession case
(define/match (-begin/simp xs)
  [((list e)) e]
  [(es) (-begin es)])

(struct -id ([name : Symbol] [ctx : Adhoc-Module-Path]) #:transparent)


;; Definition of AST subset as in Racket reference 1.2.3.1

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
            'number? 'real? 'integer? 'not 'boolean? 'string? 'symbol? 'procedure? 'keyword?)
          ;; `arity` is the number of fields in the struct
          ;; `index` is the index that this accesses
          (struct -st-ac [tag : -id] [arity : Integer] [index : Integer])
          'add1 'sub1 'string-length 'sqrt
          'sin 'cos 'tan 'abs 'round 'floor 'ceiling 'log
          ;; temporary ops
          'sqr
          )
        (subset: -o2
          'equal? '= '> '< '>= '<= '+ '- '* '/
          'expt 'abs 'min 'max
          'arity=? 'arity>=? 'arity-includes?
          'remainder 'quotient
          'set-box!)
        (struct -st-mk [tag : -id] [arity : Integer]))))
  ;; lexical variables
  (struct -x [name : Symbol])
  ;; module references
  (struct -ref [id : -id] [ctx : Mon-Party])
  (struct -@ [f : -e] [xs : (Listof -e)] [ctx : Mon-Party])
  (struct -if [i : -e] [t : -e] [e : -e])
  (struct -wcm [key : -e] [val : -e] [body : -e])
  -begin/e
  (struct -begin0 [e0 : -e] [es : (Listof -e)])
  (struct -quote [v : Any])
  (struct -let-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e] [ctx : Mon-Party])
  (struct -letrec-values [bnds : (Listof (Pairof (Listof Symbol) -e))] [body : -e] [ctx : Mon-Party])
  (struct -set! [x : Symbol] [e : -e])

  (struct -@-havoc [x : -x]) ; hack for havoc to detect argument's arity at runtime
  (struct -amb [es : (Setof -e)])
  
  ;; contract stuff
  (struct -μ/c [x : Symbol] [c : -e])
  (struct -->i [dom : (Listof (Pairof Symbol -e))] [rng : -e]) ; dependent function contract
  (struct -x/c [x : Symbol])
  (struct -struct/c [tag : -id] [fields : (Listof -e)])
  #;(-and/c [l : .e] [r : .e])
  #;(-or/c [l : .e] [r : .e])
  #;(.¬/c [c : .e]))

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
(define -void #|hack|# (-@ (-st-mk (-id 'void 'Λ) 0) '() 'Λ))
(define -null #|hack|# (-@ (-st-mk (-id 'null 'Λ) 0) '() 'Λ))
(define -box? (-st-p (-id 'box 'Λ) 1))
(define -unbox (-st-ac (-id 'box 'Λ) 1 0))
(define -box (-st-mk (-id 'box 'Λ) 1))

(: --> : (Listof -e) -e → -e)
;; Make a non-dependent contract as a special case of dependent contract
(define (--> cs d)
  (define doms
    (for/list : (Listof (Pairof Symbol -e)) ([c cs] [i (in-naturals)])
      (define x (string->symbol (format "■~a" (n-sub i)))) ; hack
      (cons x c)))
  (-->i doms d))

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
    [(-μ/c x e) (set-remove (FV e) x)]
    [(-->i doms rng)
     (define-values (bound FV_dom)
       (for/fold ([bound : (Setof Symbol) ∅] [FV_dom : (Setof Symbol) ∅]) ([dom doms])
         (match-define (cons x c) dom)
         (values (set-add bound x) (∪ FV_dom (FV c)))))
     (∪ FV_dom (-- (FV rng) bound))]
    [(-struct/c _ cs)
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
   [(-μ/c _ c) (checks# c)]
   [(-->i cs d) (+ (checks# ((inst map -e (Pairof Symbol -e)) cdr cs)) (checks# d))]
   [(-struct/c _ cs) (checks# cs)]

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
  (:* -and/c -or/c -one-of/c : -e * → -e)
  (define -and/c
    (match-lambda*
      [(list) -any/c]
      [(list c) c]
      [(cons c cs) (-@ mk-and/c (list c (apply -and/c cs)) 'Λ)]))
  (define -or/c
    (match-lambda*
      [(list) -none/c]
      [(list c) c]
      [(cons c cs) (-@ mk-or/c (list c (apply -or/c cs)) 'Λ)]))
  (define -one-of/c
    (match-lambda*
      [(list) -none/c]
      [(list e) (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) 'Λ))]
      [(cons e es) (-or/c (-λ (list 'x₀) (-@ 'equal? (list (-x 'x₀) e) 'Λ)) (apply -one-of/c es))]))
  
  (: -cons/c : -e -e → -e)
  (define (-cons/c c d) (-struct/c (-id 'cons 'Λ) (list c d)))

  (: -not/c : -e → -e)
  (define (-not/c c) (-@ (-st-mk (-id 'not/c 'Λ) 1) (list c) 'Λ)))

(: -list/c : -e * → -e)
(define (-list/c . cs) (foldr -cons/c -null/c cs))

(: -list : -e * → -e)
(define (-list . es)
  (foldr (λ ([eᵢ : -e] [es : -e]) (-@ -cons (list eᵢ es) 'Λ)) -null es))

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
  (-λ (list x) (-and (-@ 'real? (list (-x x)) 'Λ) (-@ op (list (-x x) e) 'Λ))))

(define ☠ 'havoc) ; havoc module path
(define havoc-id (-id 'havoc-id ☠)) ; havoc function id

(define (havoc-ref-from [ctx : Mon-Party])
  (-ref havoc-id ctx))

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
  (define havoc-ref (havoc-ref-from ☠))
  (define x (-x '☠))
  (define havoc-func ; only used by `verify` module, not `ce`
    (-λ (list '☠)
        (-amb/simp
         (cons (-@ havoc-ref (list (-@-havoc x)) ☠)
               (for/list : (Listof -@) ([ac (prog-accs ms)])
                 (-@ havoc-ref (list (-@ ac (list x) ☠)) ☠))))))
  (define m
    (-module ☠
             (-plain-module-begin
              (list
               (-define-values (list (-id-name havoc-id)) havoc-func)
               (-provide (list (-p/c-item (-id-name havoc-id) -any/c)))))))

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
                     (-@ (•!) (list ref) ☠))))

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

(: binder-has? : -formals Symbol → Boolean)
;; returns whether a list of binding names has given name
(define (binder-has? xs x)
  (match xs
    [(? list? xs) (and (member x xs) #t)] ; force boolean
    [(-varargs zs z) (or (equal? z x) (and (member x zs) #t))]))

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
    [(-μ/c z c) (if (equal? z x) 0 (count-xs c x))]
    [(-->i doms rng)
     (define-values (bound k)
       (for/fold ([bound : (Setof Symbol) ∅] [k : Integer 0]) ([dom doms])
         (match-define (cons z c) dom)
         (values (set-add bound z) (+ k (count-xs c x)))))
     (+ k (if (set-member? bound x) 0 (count-xs rng x)))]
    [(-struct/c _ cs) (count-xs cs x)]
    [(? list? l) (for/sum : Integer ([i l]) (count-xs i x))]
    [_ 0]))

(: -ref->e : (Listof -module) -ref → -e)
;; Search for definition in list of modules at given reference
(define (-ref->e ms ref)
  (match-define (-ref (-id name from) _) ref)
  ;; FIXME:
  ;; - TR doesn't like `for*/or` so i use nested `for/or` instead
  (define m (path->module ms from name))
  (match-define (-module _ (-plain-module-begin forms)) m)
  (or (for/or : (U #f -e) ([form (in-list forms)])
        (match form
          [(-define-values (list x) e) (and (equal? x name) e)]
          [(-define-values xs (-@ 'values vs _))
           (for/or : (U #f -e) ([x xs] [v vs] #:when (equal? x name)) v)]
          [_ #f]))
      (error 'ref->e "Module `~a` does not define `~a`" from name)))

(: -ref->ctc : (Listof -module) -ref → -e)
;; Search for contract in list of modules at given reference
(define (-ref->ctc ms ref)
  (match-define (-ref (-id name from) _) ref)
  ;; FIXME:
  ;; - TR doesn't like `for*/or` so i use nested `for/or` instead
  (define m (path->module ms from name))
  (match-define (-module _ (-plain-module-begin forms)) m)
  (or (for/or : (U #f -e) ([form (in-list forms)])
        (match form
          [(-provide specs)
           (for/or : (U #f -e) ([spec (in-list specs)])
             (match-define (-p/c-item x c) spec)
             (and (equal? x name) c))]
          [_ #f]))
      (error 'ref->ctc "Module `~a` does not provide `~a`" from name)))

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
      [(-μ/c z c) (set-remove (go c) z)]
      [(-->i cs d) (∪ (go* ((inst map -e (Pairof Symbol -e)) cdr cs)) (go d))]
      [(-struct/c t cs) (go* cs)]
      [(-x/c x) (set x)]
      [_ ∅]))
  
  (go e))

(: id/c : -id → -id)
;; HACK
(define (id/c id)
  (match-define (-id name path) id)
  (-id (string->symbol (format "~a/c" name)) path))
