#lang typed/racket
(require "utils.rkt")
(provide (all-defined-out))

(define-type Symbol^3 (List Symbol Symbol Symbol))

;; prefixing types with dots just so i can use 1-letter variables without shadowing them

;; program and module
(struct .p ([modules : .m*] [accessors : (Setof .st-ac)] [main : .e]) #:transparent)
(struct .m* ([order : (Listof Symbol)] [modules : (Map Symbol .m)]) #:transparent)
(struct .m ([order : (Listof Symbol)] [defs : (Map Symbol (Pairof .e (U #f .e)))]) #:transparent)

;; expression
(define-data .e
  (subset: .v
    (struct .λ [arity : Integer] [body : .e] [var? : Boolean])
    (subset: .•
      '•
      (struct .•ₗ [l : Negative-Integer]))
    (subset: .prim
      (struct .b [unboxed : (U Number Boolean String Symbol)])
      (subset: .o
        (subset: .o1
          (subset: .pred
            (struct .st-p [tag : Symbol] [arity : Integer])
            'number? 'real? 'integer? 'true? 'false? 'boolean? 'string? 'symbol? 'procedure?)
          (struct .st-ac [tag : Symbol] [arity : Integer] [index : Integer])
          'add1 'sub1 'string-length 'sqrt)
        (subset: .o2
          'equal? '= '> '< '>= '<= '+ '- '* '/
          'expt 'abs 'min 'max
          'arity=? 'arity>=? 'arity-includes?
          'set-box!)
        (struct .st-mk [tag : Symbol] [arity : Integer]))))
  (struct .x [sd : Integer]) ; static distance
  (struct .ref [name : Symbol] [in : Symbol] [ctx : Symbol])
  (struct .@ [f : .e] [xs : (Listof .e)] [ctx : Symbol])
  (struct .@-havoc [x : .x]) ; hack for havoc
  (struct .if [i : .e] [t : .e] [e : .e])
  (struct .amb [e* : (Setof .e)])
  ; contract stuff
  (struct .μ/c [x : Symbol] [c : .e])
  (struct .λ/c [xs : (Listof .e)] [cy : .e] [var? : Boolean])
  (struct .x/c [x : Symbol])
  (struct .struct/c [tag : Symbol] [fields : (Listof .e)]))

(: •! : → .•ₗ)
;; Generate new labeled hole
(define •!
  (let ([n : Negative-Integer -2 #|HACK|#])
    (λ () (begin0 (.•ₗ n) (set! n (- n 1))))))

(: FV : (case→ [.e → (Setof Integer)]
               [.e Integer → (Setof Integer)]))
(define (FV e [d 0])
  (match e
    [(.x sd) (if (>= sd d) {set (- sd d)} ∅)]
    [(.λ n e _) (FV e (+ d n))]
    [(.@ f xs _) (for/fold ([FVs (FV f d)]) ([x xs])
                   (set-union FVs (FV x d)))]
    [(.@-havoc x) (FV x d)]
    #;[(.apply f xs _) (set-union (FV f d) (FV xs d))]
    [(.if e e1 e2) (set-union (FV e d) (FV e1 d) (FV e2 d))]
    [(.amb e*) (for/fold ([FVs : (Setof Integer) ∅]) ([e e*])
                 (set-union FVs (FV e d)))]
    [(.μ/c _ e) (FV e d)]
    [(.λ/c cx cy _) (for/fold ([FVs (FV cy (+ d (length cx)))]) ([c cx])
                      (set-union FVs (FV c d)))]
    [(.struct/c _ cs) (for/fold ([FVs : (Setof Integer) ∅]) ([c cs])
                        (set-union FVs (FV c d)))]
    [_ ∅]))

(: closed? : .e → Boolean)
(define (closed? e) (set-empty? (FV e)))

(: checks# : (Rec X (U .e .p .m (Listof X))) → Integer)
(define checks#
  (match-lambda
    [(? list? es) (for/sum ([e es]) (checks# e))]
    [(.p (.m* _ ms) _ e) (+ (ann (for/sum ([(l mi) (in-hash ms)]
                                           #:unless (equal? l '☠))
                                   (checks# mi)) Integer)
                            (checks# e))]
    [(.m _ defs) (for/sum ([(l d) (in-hash defs)])
                   (match-let ([(cons e c) d])
                     (+ (checks# e) (match c [(? .e? c) (checks# c)] [_ 0]))))]
    [(.λ _ e _) (checks# e)]
    [(.@ f xs _) (+ 1 (checks# f) (checks# xs))]
    [(.@-havoc x) 1]
    [(.if e e1 e2) (+ (checks# e) (checks# e1) (checks# e2))]
    [(.amb e*) (for/sum ([e e*]) (checks# e))]
    [(.μ/c _ e) (checks# e)]
    [(.λ/c cx cy _) (+ (checks# cx) (checks# cy))]
    [(.struct/c _ cs) (checks# cs)]
    [(or (? .pred?) (? .st-mk?)) 0]
    [(? .o1?) 1]
    [(? .o2?) 2]
    [(? .o?) 1]
    [_ 0]))

;; frequently used constants
(define .tt (.b #t))
(define .ff (.b #f))
(define .any/c (.λ 1 .tt #f))
(define .none/c (.λ 1 .ff #f))
(define .empty/c (.st-p 'empty 0))
(define .car (.st-ac 'cons 2 0))
(define .cdr (.st-ac 'cons 2 1))
(define .zero (.b 0))
(define .one (.b 1))
(define .void (.@ (.st-mk 'void 0) (list) 'Λ))

(: .cons/c : .e .e → .e)
(define (.cons/c c d) (.struct/c 'cons (list c d)))

(:* [.or/c .and/c] : Symbol (Listof .e) → .e)
(define (.or/c l e*)
  (match e*
    ['() .none/c]
    [(list c) c]
    [(cons c cr) (.@ (.st-mk 'or/c 2) (list c (.or/c l cr)) l)]))
(define (.and/c l e*)
  (match e*
    ['() .any/c]
    [(list c ) c]
    [(cons c cr) (.@ (.st-mk 'and/c 2) (list c (.and/c l cr)) l)]))
(: .not/c : Symbol .e → .e)
(define (.not/c l c)
  (.@ (.st-mk '¬/c 1) (list c) l))

(: prim : (U Symbol Number String Boolean) → (U #f .e))
(define prim
  (match-lambda
   #|['box (.st-mk 'box 1)]
   ['box? (.st-p 'box 1)]
   ['unbox (.st-ac 'box 1 0)]
   ['set-box! (.set-box!)]|#
   ['not 'false?]
   [(or 'box 'box? 'unbox 'set-box!)
    (error 'Disabled "Box operations are not supported for now")]
   [(? .o? o) o]
   ['any/c .any/c]
   ['none/c .none/c]
   ['cons? (.st-p 'cons 2)]
   ['cons (.st-mk 'cons 2)]
   ['car .car]
   ['cdr .cdr]
   [(or 'empty 'null) (.@ (.st-mk 'empty 0) empty 'Λ)]
   [(or 'empty? 'null?) .empty/c]
   ['void (.st-mk 'void 0)]
   [(? number? x) (.b x)]
   [#f .ff]
   [#t .tt]
   [(? string? x) (.b x)]
   #;[`(quote ,(? sym? x)) (.b x)]
   [_ #f]))

(: name : .o → Symbol)
(define name
  (match-lambda
   [(? symbol? s) s]
   [(.st-mk t _) t]
   [(.st-ac 'cons 2 0) 'car]
   [(.st-ac 'cons 2 1) 'cdr]
   [(.st-ac 'box 1 0) 'unbox]
   [(.st-ac t _ i) (string->symbol (format "~a@~a" t i))]
   [(.st-p t _) (string->symbol (format "~a?" t))]))

(define .pred/c (.λ/c (list .any/c) 'boolean? #f))

(: ¬l : Symbol^3 → Symbol^3)
(define ¬l
  (match-lambda [(list l+ l- lo) (list l- l+ lo)]))

(: gen-accs : (Sequenceof .m) → (Setof .st-ac))
(define (gen-accs ms)
  (for*/fold ([acs : (Setof .st-ac) {set .car .cdr}])
             ([m ms]
              [defs (in-value (.m-defs m))]
              [d (in-hash-values defs)]
              [c (in-value (cdr d))]
              #:when (match? c (.λ/c _ (? .struct/c?) _)))
    (match-define (.λ/c _ (.struct/c t cs) _) c)
    (define n (length cs))
    (for/fold ([acs acs]) ([i n])
      (set-add acs (.st-ac t n i)))))

(: gen-havoc : .p → .p)
(define (gen-havoc p)
  (match-define (.p (.m* m-seq ms) acs e†) p)

  (define havoc
    (.λ 1 (.amb (set-add (for/set: .@ ([ac acs])
                           (.@ (.ref 'havoc '☠ '☠)
                               (list (.@ ac (list (.x 0)) '☠)) '☠))
                         (.@ (.ref 'havoc '☠ '☠)
                             (list (.@-havoc (.x 0))) '☠))) #f))

  (define ☠ (.m (list 'havoc)
                (hash-set (ann #hash() (Map Symbol (Pairof .e (U #f .e))))
                          'havoc (cons havoc (.λ/c (list .any/c) .none/c #f)))))

  (if (hash-has-key? ms '☠) p
      (.p (.m* (cons '☠ m-seq) (hash-set ms '☠ ☠)) acs e†)))

(: amb : (Listof .e) → .e)
#;(define (amb e*)
  (define s
    (for/fold ([ac : (Setof .e) ∅]) ([e e*])
      (match e ; try to avoid nested amb
        [(.amb s) (set-union ac s)]
        [_ (set-add ac e)])))
  (cond [(= 1 (set-count s)) (set-first s)]
        [else (.amb s)]))
(define (amb e*)
  (match e*
    ['() .ff]
    [(list e) e]
    [(cons e es) (.if (•!) e (amb es))]))

(: e/ : .e Integer .e → .e)
;; Substitute expression at given static distance
(define (e/ e x eₓ)
  (match e
    [(.x k) (if (= k x) eₓ e)]
    [(.λ n e v?) (.λ n (e/ e (+ x (if v? (- n 1) n)) eₓ) v?)]
    [(.@ f xs l) (.@ (e/ f x eₓ) (for/list : (Listof .e) ([xᵢ xs]) (e/ xᵢ x eₓ)) l)]
    [(.if e e₁ e₂) (.if (e/ e x eₓ) (e/ e₁ x eₓ) (e/ e₂ x eₓ))]
    [(.amb es) (.amb (for/set: .e ([eᵢ es]) (e/ eᵢ x eₓ)))]
    [(.μ/c z c) (.μ/c z (e/ c x eₓ))]
    [(.λ/c cs cy v?) (.λ/c (for/list : (Listof .e) ([c cs]) (e/ c x eₓ))
                           (e/ cy (+ x (if v? (- (length cs) 1) (length cs))) eₓ)
                           v?)]
    [(.struct/c t cs) (.struct/c t (for/list : (Listof .e) ([c cs]) (e/ c x eₓ)))]
    [e e]))

(: count-xs : .e Integer → Integer)
;; Count occurences of variable (given as static distance)
(define (count-xs e x)
  (match e
    [(.x k) (if (= k x) 1 0)]
    [(.λ n e v?) (count-xs e (+ x (if v? (- n 1) n)))]
    [(.@ f xs _) (+ (count-xs f x)
                    (for/sum : Integer ([xᵢ xs]) (count-xs xᵢ x)))]
    [(.if e e₁ e₂) (+ (count-xs e x) (count-xs e₁ x) (count-xs e₂ x))]
    [(.amb es) (for/sum : Integer ([e es]) (count-xs e x))]
    [(.μ/c _ c) (count-xs c x)]
    [(.λ/c cs cy v?)
     (+ (for/sum : Integer ([c cs]) (count-xs c x))
        (count-xs cy (+ x (if v? (- (length cs) 1) (length cs)))))]
    [(.struct/c _ cs) (for/sum : Integer ([c cs]) (count-xs c x))]
    [_ 0]))
