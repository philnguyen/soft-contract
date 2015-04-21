#lang typed/racket
(require racket/splicing "utils.rkt"
         (for-syntax racket/base racket/syntax))
(provide (all-defined-out))

;; prefixing types with dots just so i can use 1-letter variables without shadowing them

(struct (X) .begin ([body : (Listof X)]) #:transparent)
(define-type .begin/expr (.begin .expr))
(define-type .begin/top (.begin .top-level-form))

(define-type/pred Adhoc-Module-Path (U Symbol String) #|TODO|#)
(define-type Mon-Party Adhoc-Module-Path)
(define-type Mon-Info (List Mon-Party Mon-Party Mon-Party))

(: swap-parties : Mon-Info → Mon-Info)
(define/match (swap-parties info)
  [((list + - o)) (list - + o)])

;;(define THE-MODULE-HACK : Module-Path "The-Module")

(: -begin : (∀ (X) (Listof X) → (U X (.begin X))))
(define/match (-begin xs)
  [((list e)) e]
  [(es) (.begin es)])

(struct .id ([name : Symbol] [from : Adhoc-Module-Path]) #:transparent)

;; Subset of Racket reference 1.2.3.1

(define-data .top-level-form
  .general-top-level-form
  .expr
  .module
  .begin/top)

(define-data .module-level-form
  .general-top-level-form
  (struct .provide [specs : (Listof .provide-spec)])
  .submodule-form)

(define-data .general-top-level-form
  .expr
  (struct .define-values [ids : (Listof Symbol)] [e : .expr])
  (struct .require [specs : (Listof .require-spec)]))

(define-data .submodule-form
  (struct .module [path : Adhoc-Module-Path] [body : .plain-module-begin]))

(define-data .provide-spec
  (struct .p/c-item [id : Symbol] [spec : .expr] #|TODO|#))

(define-data .require-spec
  Adhoc-Module-Path #|TODO|#)

(struct .plain-module-begin ([body : (Listof .module-level-form)]) #:transparent)

(define-data .expr
  (subset: .v
    ;; if `var?` is true, accepts >= arity args
    (struct .λ [formals : .formals] [body : .expr])
    (struct .case-lambda [body : (Listof (Pairof .formals .expr))])
    (subset: .•
      '•
      ;; `l` is a tag annotating which static location this opaque value came from
      (struct .•ₗ [l : Negative-Integer]))
    (subset: .prim
      ;; primitive values that can appear in syntax
      (struct .b [unboxed : (U Number Boolean String Symbol Keyword #|Sexp Bytes Regexp PRegexp|#)])
      (subset: .o
        'values
        (subset: .o1
          (subset: .pred
            ;; `arity` is the number of fields in the struct
            (struct .st-p [tag : .id] [arity : Integer])
            'number? 'real? 'integer? 'false? 'boolean? 'string? 'symbol? 'procedure? 'keyword?)
          ;; `arity` is the number of fields in the struct
          ;; `index` is the index that this accesses
          (struct .st-ac [tag : .id] [arity : Integer] [index : Integer])
          'add1 'sub1 'string-length 'sqrt
          'sin 'cos 'tan 'abs 'round 'floor 'ceiling 'log )
        (subset: .o2
          'equal? '= '> '< '>= '<= '+ '- '* '/
          'expt 'abs 'min 'max
          'arity=? 'arity>=? 'arity-includes?
          'remainder 'quotient
          'set-box!)
        (struct .st-mk [tag : .id] [arity : Integer]))))
  ;; lexical variables
  (struct .x #|static distance|# [sd : Integer])
  ;; module references
  (struct .ref [id : .id] [ctx : Mon-Party])
  (struct .@ [f : .expr] [xs : (Listof .expr)] [ctx : Mon-Party])
  (struct .if [i : .expr] [t : .expr] [e : .expr])
  (struct .wcm [key : .expr] [val : .expr] [body : .expr])
  .begin/expr #;(struct .begin [exprs : (Listof .general-top-level-form)])
  (struct .begin0 [expr0 : .expr] [exprs : (Listof .expr)])
  (struct .quote [v : Any])
  ;; the Integer in `bnds` is the number of identifiers bound in that clause
  (struct .let-values [bnds : (Listof (Pair Integer .expr))] [body : .expr] [ctx : Mon-Party])
  ;; the Integer in `bnds` is the number of identifiers bound in that clause
  (struct .letrec-values [bnds : (Listof (Pair Integer .expr))] [body : .expr] [ctx : Mon-Party])

  (struct .@-havoc [x : .x]) ; hack for havoc to detect argument's arity at runtime
  (struct .amb [es : (Setof .expr)])
  ; contract stuff
  (struct .μ/c [x : Symbol] [c : .expr])
  (struct .-> [dom : (Listof .expr)] [rng : .expr]) ; non-dependent function contract
  (struct .->i [xs : (Listof .expr)] [cy : .expr] [var? : Boolean]) ; dependent function contract
  (struct .x/c [x : Symbol])
  (struct .struct/c [tag : .id] [fields : (Listof .expr)])
  #;(.and/c [l : .e] [r : .e])
  #;(.or/c [l : .e] [r : .e])
  #;(.¬/c [c : .e]))

(define-syntax (define-value/pattern stx)
  (syntax-case stx ()
    [(_ x pat)
     (with-syntax ([@x (format-id #'x "?~a" #'x)])
       #'(begin
           (define x pat)
           (define-match-expander @x
             (syntax-rules ()
               [(_) pat]))))]))

;; frequently used constants
(define .x₀ (.x 0))
(define-value/pattern .tt (.b #t))
(define-value/pattern .ff (.b #f))
(define-value/pattern .any/c (.λ 1 .tt))
(define-value/pattern .none/c (.λ 1 .ff))
(define-value/pattern .null/c (.st-p (.id 'null 'Λ) 0))
(define-value/pattern .cons (.st-mk (.id 'cons 'Λ) 2))
(define-value/pattern .car (.st-ac (.id 'cons 'Λ) 2 0))
(define-value/pattern .cdr (.st-ac (.id 'cons 'Λ) 2 1))
(define-value/pattern .cons? (.st-p (.id 'cons 'Λ) 2))
(define-value/pattern .zero (.b 0))
(define-value/pattern .one (.b 1))
(define-value/pattern .void (.st-mk (.id 'void 'Λ) 0))
(define-value/pattern .null #|hack|# (.@ (.st-mk (.id 'null 'Λ) 0) (list) 'Λ))
(define-value/pattern .box? (.st-p (.id 'box 'Λ) 1))
(define-value/pattern .unbox (.st-ac (.id 'box 'Λ) 1 0))
(define-value/pattern .box (.st-mk (.id 'box 'Λ) 1))

;; Current restricted representation of program
(struct .prog ([modules : (Listof .module)] [main : .expr]) #:transparent)

(define-type/pred .formals (U Integer (Pairof Integer 'rest)))

(: •! : → .•ₗ)
;; Generate new labeled hole
(define •!
  (let ([n : Negative-Integer -2 #|HACK don't fix|#])
    (λ () (begin0 (.•ₗ n) (set! n (- n 1))))))

(: FV : ([.expr] [Integer] . ->* . (Setof Integer)))
;; Compute free variables for expression. Return set of static distances.
(define (FV e [d 0])
  (match e
    [(.x sd) (if (>= sd d) {set (- sd d)} ∅)]
    [(.λ xs e) (match xs
                 [(? integer? n) (FV e (+ d n))]
                 [(cons n _) (FV e (+ d n 1))])]
    [(.@ f xs _) (for/fold ([FVs (FV f d)]) ([x xs])
                   (set-union FVs (FV x d)))]
    [(.let-values bnds e _)
     (define-values (δ xs)
       (for/fold ([δ : Integer 0] [xs : (Setof Integer) ∅]) ([bnd bnds])
         (match-define (cons n eₓ) bnd)
         (values (+ δ n) (set-union xs (FV eₓ d)))))
     (set-union xs (FV e (+ δ d)))]
    [(.letrec-values bnds e _)
     (define δ : Integer (for/sum ([bnd bnds]) (car bnd)))
     (define d′ (+ δ d))
     (apply set-union
            (FV e d′)
            (for/list : (Listof (Setof Integer)) ([bnd bnds])
              (FV (cdr bnd) d′)))
     (todo 'letrec-values)]
    [(.@-havoc x) (FV x d)]
    #;[(.apply f xs _) (set-union (FV f d) (FV xs d))]
    [(.if e e1 e2) (set-union (FV e d) (FV e1 d) (FV e2 d))]
    [(.amb es) (for/fold ([FVs : (Setof Integer) ∅]) ([e es])
                 (set-union FVs (FV e d)))]
    [(.μ/c _ e) (FV e d)]
    [(.->i cx cy _) (for/fold ([FVs (FV cy (+ d (length cx)))]) ([c cx])
                      (set-union FVs (FV c d)))]
    [(.struct/c _ cs) (for/fold ([FVs : (Setof Integer) ∅]) ([c cs])
                        (set-union FVs (FV c d)))]
    [_ (log-debug "FV(~a) = ∅~n" e) ∅]))

(: shift-FV : .expr Integer → .expr)
;; Shift free-variables in expression by given amount
(define (shift-FV e d)
  (let go ([d₀ 0] [e e])
    (match e
      [(.x sd) (if (>= sd d₀) (.x (+ sd d)) e)]
      [(.λ xs e) (match xs
                   [(? integer? n) (.λ xs (go (+ d₀ n) e))]
                   [(cons n _) (.λ xs (go (+ d₀ 1 n) e))])]
      [(.@ f xs ctx) (.@ (go d₀ f) (map (curry go d₀) xs) ctx)]
      [(.let-values bnds e ctx)
       (define-values (δ bnds-rev)
         (for/fold ([δ : Integer 0] [bnds-rev : (Listof (Pairof Integer .expr)) '()])
                   ([bnd bnds])
           (match-define (cons nₓ eₓ) bnd)
           (values (+ δ nₓ) (cons (cons nₓ (go d₀ eₓ)) bnds-rev))))
       (.let-values (reverse bnds-rev)
                    (go (+ d₀ δ) e)
                    ctx)]
      [(.@-havoc x) (.@-havoc (assert (go d₀ x) .x?))]
      [(.if e e₁ e₂) (.if (go d₀ e) (go d₀ e₁) (go d₀ e₂))]
      [(.amb es) (.amb (for/set: : (Setof .expr) ([e es])
                         (go d₀ e)))]
      [(.μ/c x e) (.μ/c x (go d₀ e))]
      [(.->i cx cy #f)
       (.->i (map (curry go d₀) cx) (go (+ d₀ (length cx)) cy) #f)]
      [(.struct/c t cs) (.struct/c t (map (curry go d₀) cs))]
      [e (log-debug "shift-FV⟦~a⟧ = ~a~n" e e) e])))

(define (closed? [e : .expr]) (set-empty? (FV e)))

(: checks# : (Rec X (U .top-level-form
                       .expr
                       .general-top-level-form
                       .expr
                       .module
                       .begin/top
                       .plain-module-begin
                       .module-level-form
                       .prog
                       (Listof X))) → Integer)
;; Statically count number of unsafe operations needing checks
(define checks#
  (match-lambda
   [(? list? es) (for/sum : Integer ([e (in-list es)]) (checks# e))]
   [(.prog ms e) (+ (checks# ms) (checks# e))]
   [(.define-values _ e) (checks# e)]
   [(.λ _ e) (checks# e)]
   [(.@ f xs _) (+ 1 (checks# f) (checks# xs))]
   [(.if i t e) (+ (checks# i) (checks# t) (checks# e))]
   [(.wcm k v e) (+ (checks# k) (checks# v) (checks# e))]
   [(.begin0 e es) (+ (checks# e) (checks# es))]
   [(.let-values bindings e _)
    (+ (for/sum : Integer ([binding (in-list bindings)])
         (match-define (cons _ eₓ) binding)
         (checks# eₓ))
       (checks# e))]
   [(.letrec-values bindings e _)
    (+ (for/sum : Integer ([binding (in-list bindings)])
         (match-define (cons _ eₓ) binding)
         (checks# eₓ))
       (checks# e))]
   [(.amb es) (for/sum ([e (in-set es)]) (checks# e))]
   [(.μ/c _ c) (checks# c)]
   [(.->i cs d _) (+ (checks# cs) (checks# d))]
   [(.struct/c _ cs) (checks# cs)]

   [(.plain-module-begin xs) (checks# xs)]
   [(.module _ body) (checks# body)]
   [(or (? .pred?) (? .st-mk?)) 0]
   [(? .o1?) 1]
   [(? .o2?) 2]
   [_ 0]))

;; TODO: ok to use 'Λ as context? Never blamed?
(splicing-let ([mk-and/c (.st-mk (.id 'and/c 'Λ) 2)]
               [mk-or/c (.st-mk (.id 'or/c 'Λ) 2)]
               [mk-cons/c (.st-mk (.id 'cons/c 'Λ) 2)]
               [mk-not/c (.st-mk (.id 'not/c 'Λ) 1)])
  (:* .and/c .or/c .one-of/c : .expr * → .expr)
  (define .and/c
    (match-lambda*
      [(list) .any/c]
      [(list c) c]
      [(cons c cs) (.@ mk-and/c (list c (apply .and/c cs)) 'Λ)]))
  (define .or/c
    (match-lambda*
      [(list) .none/c]
      [(list c) c]
      [(cons c cs) (.@ mk-or/c (list c (apply .or/c cs)) 'Λ)]))
  (define .one-of/c
    (match-lambda*
      [(list) .none/c]
      [(list e) (.λ 1 (.@ 'equal? (list .x₀ e) 'Λ))]
      [(cons e es) (.or/c (.λ 1 (.@ 'equal? (list .x₀ e) 'Λ)) (apply .one-of/c es))]))
  
  (: .cons/c : .expr .expr → .expr)
  (define (.cons/c c d) (.struct/c (.id 'cons 'Λ) (list c d)))

  (: .not/c : .expr → .expr)
  (define (.not/c c) (.@ (.st-mk (.id 'not/c 'Λ) 1) (list c) 'Λ)))

(: .list/c : .expr * → .expr)
(define (.list/c . cs) (foldr .cons/c .null/c cs))

(: .list : .expr * → .expr)
(define (.list . es)
  (foldr (λ ([eᵢ : .expr] [es : .expr]) (.@ .cons (list eᵢ es) 'Λ)) .null es))

;; Macros
(:* .and .or : .expr * → .expr)
(define .and
  (match-lambda*
    [(list) .tt]
    [(list e) e]
    [(cons e es) (.if e (apply .and es) .ff)]))
(define .or
  (match-lambda*
    [(list) .ff]
    [(list e) e]
    [(cons e es) (.let (list e) (.if .x₀ .x₀ (apply .or es)))]))

(: .comp/c : .o2 .expr → .expr)
(define (.comp/c op e)
  (.λ 1 (.and (.@ 'real? (list .x₀) 'Λ) (.@ op (list .x₀ (shift-FV e 1)) 'Λ))))

(: .let : (Listof .expr) .expr → .expr)
(define (.let xs e) ; FIXME expand to let-values instead
  (.@ (.λ (length xs) e) xs 'Λ))

(: name : .o → Symbol)
(define name
  (match-lambda
   [(? symbol? s) s]
   [(.st-mk (.id t _) _) t]
   [(.st-ac (.id 'cons 'Λ) 2 0) 'car]
   [(.st-ac (.id 'cons 'Λ) 2 1) 'cdr]
   [(.st-ac (.id 'box 'Λ) 1 0) 'unbox]
   [(.st-ac (.id t _) _ i) (string->symbol (format "~a@~a" t i))]
   [(.st-p (.id t _) _) (string->symbol (format "~a?" t))]))

#;(define .pred/c (.->i (list .any/c) 'boolean? #f))

#;(: gen-accs : (Sequenceof .m) → (Setof .st-ac))
#;(define (gen-accs ms)
  (for*/fold ([acs : (Setof .st-ac) {set .car .cdr}])
             ([m ms]
              [defs (in-value (.m-defs m))]
              [d (in-hash-values defs)]
              [c (in-value (cdr d))]
              #:when (match? c (.->i _ (? .struct/c?) _)))
    (match-define (.->i _ (.struct/c t cs) _) c)
    (define n (length cs))
    (for/fold ([acs acs]) ([i n])
      (set-add acs (.st-ac t n i)))))

(define ☠ 'havoc) ; havoc module path
(define havoc-id (.id 'havoc-id ☠)) ; havoc function id

(define (havoc-ref-from [ctx : Mon-Party])
  (.ref havoc-id ctx))

(: prog-accs : (Listof .module) → (Setof .st-ac))
;; Retrieve set of all public accessors from program
(define (prog-accs ms)
  ;; FIXME: generate accessors properly
  {set})

(: gen-havoc : (Listof .module) → (Values .module .expr))
;; Generate:
;; - havoc module
;; - expression havoc-ing exported identifiers from all concrete modules
(define (gen-havoc ms)

  ;;; Generate module
  (define havoc-ref (havoc-ref-from ☠))
  (define havoc-func ; only used by `verify` module, not `ce`
    (.λ 1 (-amb
           (cons (.@ havoc-ref (list (.@-havoc .x₀)) ☠)
                 (for/list : (Listof .@) ([ac (prog-accs ms)])
                   (.@ havoc-ref (list (.@ ac (list .x₀) ☠)) ☠))))))
  (define m
    (.module ☠
             (.plain-module-begin
              (list
               (.define-values (list (.id-name havoc-id)) havoc-func)
               (.provide (list (.p/c-item (.id-name havoc-id) .any/c)))))))

  ;;; Generate expression
  (define-set refs : .ref)
  #;(log-debug "~nmodules: ~n~a~n" ms)
  (for* ([m (in-list ms)])
    (cond
     [(module-opaque? m)
      (eprintf "Omit havocking opaque module ~a~n" (.module-path m))]
     [else
      #;(log-debug "Havocking transparent module ~a~n" (.module-path m))
      (match-define (.module path (.plain-module-begin forms)) m)
      #;(eprintf "Insert exported identifiers from module ~a to unknown contexts~n" path)
      (for* ([form (in-list forms)]
             #:when (.provide? form)
             [spec (in-list (.provide-specs form))])
        #;(log-debug "adding: ~a~n" (.p/c-item-id spec))
        (refs-add! (.ref (.id (.p/c-item-id spec) path) '†)))]))
  #;(log-debug "~nrefs: ~a~n" refs)
  (define expr
    (-amb/remember (for/list ([ref (in-set refs)])
                     (.@ (•!) (list ref) ☠))))

  #;(log-debug "~nhavoc-expr:~n~a" expr)

  (values m expr))

(: -amb : (Listof .expr) → .expr)
(define (-amb es)
  (cond
    [(null? es) .ff]
    [(null? (cdr es)) (car es)]
    [else (.amb (list->set es))]))

(: -amb/remember : (Listof .expr) → .expr)
(define/match (-amb/remember es)
  [((list)) .ff]
  [((list e)) e]
  [((cons e es)) (.if (•!) e (-amb/remember es))])

(: e/ : (case->
         [.expr Integer .expr → .expr]
         [(Listof .expr) Integer .expr → (Listof .expr)]))
;; Substitute expression at given static distance
(define (e/ e x eₓ)
  (match e
    [(.x k) (if (= k x) eₓ e)]
    [(.λ (? integer? n) e) (.λ n (e/ e (+ x n) eₓ))]
    [(.λ (cons n _) e) (.λ (cons n 'rest) (e/ e (+ x n -1) eₓ))]
    [(.@ f xs l) (.@ (e/ f x eₓ) (e/ xs x eₓ) l)]
    [(.if e e₁ e₂) (.if (e/ e x eₓ) (e/ e₁ x eₓ) (e/ e₂ x eₓ))]
    [(.amb es) (.amb (for/set: : (Setof .expr) ([eᵢ es]) (e/ eᵢ x eₓ)))]
    [(.μ/c z c) (.μ/c z (e/ c x eₓ))]
    [(.-> cs d) (.-> (e/ cs x eₓ) (e/ d x eₓ))]
    [(.->i cs cy v?)
     (.->i (e/ cs x eₓ)
           (e/ cy (+ x (if v? (- (length cs) 1) (length cs))) eₓ)
           v?)]
    [(.struct/c t cs) (.struct/c t (e/ cs x eₓ))]
    [(list es ...) (for/list : (Listof .expr) ([e es]) (e/ e x eₓ))]
    [e e]))

;; FIXME: factor this out into function checking given `.module`xpr
(: module-opaque? : .module → Boolean)
(define (module-opaque? m) ; TODO: expensive?
  (match-define (.module _ (.plain-module-begin body)) m)

  (define-values (exports defines)
    (for/fold ([exports : (Setof Symbol) ∅] [defines : (Setof Symbol) ∅])
              ([e (in-list body)])
      (match e
        [(.provide specs)
         (values (set-union exports (list->set (map .p/c-item-id specs))) defines)]
        [(.define-values xs _)
         (values exports (set-union defines (list->set xs)))]
        [_ (values exports defines)])))
  (not
   (for/and : Boolean ([exported-id : Symbol (in-set exports)])
     (for/or : Boolean ([defined-id : Symbol (in-set defines)])
       (equal? exported-id defined-id)))))

(: count-xs : (U .expr (Listof .expr)) Integer → Integer)
;; Count occurences of variable (given as static distance)
(define (count-xs e x)
  (match e
    [(.x k) (if (= k x) 1 0)]
    [(.λ n e)
     (match n
       [(? integer? n) (count-xs e (+ x n))]
       [(cons n _) (count-xs e (+ x 1 n))])]
    [(.case-lambda clauses)
     (for/sum : Integer ([clause clauses])
       (match-define (cons n e) clause)
       (match n
         [(? integer? n) (count-xs e (+ x n))]
         [(cons n _) (count-xs e (+ x 1 n))]))]
    [(.@ f xs _) (+ (count-xs f x) (count-xs xs x))]
    [(.if e e₁ e₂) (+ (count-xs e x) (count-xs e₁ x) (count-xs e₂ x))]
    [(.wcm k v b) (+ (count-xs k x) (count-xs v x) (count-xs b x))]
    [(.begin es) (count-xs es x)]
    [(.let-values bindings body _)
     (define-values (count-occs count-bindings)
       (for/fold ([count-occs : Integer 0] [count-bindings : Integer 0])
                 ([binding bindings])
         (match-define (cons n e) binding)
         (values (+ count-occs (count-xs e x))
                 (+ count-bindings n))))
     (+ count-occs (count-xs body (+ x count-bindings)))]
    [(.letrec-values bindings body _)
     (define count-bindings
       (for/sum : Integer ([binding bindings]) (car binding)))
     (define δ (+ x count-bindings))
     (define count-occs
       (for/sum : Integer ([binding bindings])
         (count-xs (cdr binding) δ)))
     (+ count-occs (count-xs body δ))]
    [(.@-havoc (.x k)) (if (= k x) 1 0)]
    [(.amb es) (for/sum : Integer ([e es]) (count-xs e x))]
    [(.μ/c _ c) (count-xs c x)]
    [(.-> cs d) (+ (count-xs cs x) (count-xs d x))]
    [(.->i cs d #f) (+ (count-xs cs x) (count-xs d (+ x (length cs))))]
    [(.struct/c _ cs) (count-xs cs x)]
    [(? list? l) (for/sum : Integer ([i l]) (count-xs i x))]
    [_ 0]))

(: .ref->expr : (Listof .module) .ref → .expr)
(define (.ref->expr ms ref)
  (match-define (.ref (.id name from) _) ref)
  ;; FIXME:
  ;; - TR doesn't like `for*/or` so i use nested `for/or` instead
  (define m (path->module ms from))
  (match-define (.module _ (.plain-module-begin forms)) m)
  (or (for/or : (U #f .expr) ([form (in-list forms)])
        (match form
          [(.define-values (list x) e) (and (equal? x name) e)]
          [(.define-values xs (.@ 'values vs _))
           (cond [(index-of xs name) => (λ ([i : Integer]) (list-ref vs i))]
                 [else #f])]
          [_ #f]))
      (error 'ref->expr "Module `~a` does not define `~a`" from name)))

(: .ref->ctc : (Listof .module) .ref → .expr)
(define (.ref->ctc ms ref)
  (match-define (.ref (.id name from) _) ref)
  ;; FIXME:
  ;; - TR doesn't like `for*/or` so i use nested `for/or` instead
  (define m (path->module ms from))
  (match-define (.module _ (.plain-module-begin forms)) m)
  (or (for/or : (U #f .expr) ([form (in-list forms)])
        (match form
          [(.provide specs)
           (for/or : (U #f .expr) ([spec (in-list specs)])
             (match-define (.p/c-item x c) spec)
             (and (equal? x name) c))]
          [_ #f]))
      (error 'ref->ctc "Module `~a` does not provide `~a`" from name)))

(: path->module : (Listof .module) Adhoc-Module-Path → .module)
(define (path->module ms x)
  ;; - figure out module-path properly
  (or (for/or : (U #f .module) ([m (in-list ms)] #:when (equal? (.module-path m) x))
        m)
      (error 'path->module "Cannot find module `~a`" x)))
