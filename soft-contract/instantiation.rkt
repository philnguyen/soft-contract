#lang typed/racket/base

(require
 racket/match racket/set
 "utils/set.rkt" "utils/debug.rkt" "utils/untyped-macros.rkt" "utils/pretty.rkt"
 "ast/definition.rkt" "ast/meta-functions.rkt"
 "runtime/path-inv.rkt" "runtime/simp.rkt"
 "proof-relation/local.rkt" "proof-relation/ext/z3.rkt")

(provide instan)

(: instan : -Γ (HashTable -e Base) -e → -e)
;; Instantiate value for `e`, given path invariant and `mappings` from external solver
(define (instan Γ mappings e)
  (begin
    (dbg 'inst "instantiate:~n")
    (dbg 'inst "  Γ: ~a~n" (show-Γ Γ))
    (dbg 'inst "  mappings: ~a~n" mappings)
    (dbg 'inst "  e: ~a~n" (show-e e)))

  (match-define (-Γ _ φs) Γ)

  (let go ([e e])
    (cond
      [(hash-ref mappings e #f) => -b]
      [else
       (match e
         [(-λ xs e*) (-λ xs (go e*))]
         [(-case-λ clauses)
          (-case-λ (for/list : (Listof (Pairof -formals -e)) ([clause clauses])
                     (match-define (cons xs e*) clause)
                     (cons xs (go e*))))]
         [(? -•? v)
          (cond
            [(concretized? Γ v) => go]
            [else (blind-guess Γ mappings v)])]
         [(-@ f xs loc)
          (define xs* (map go xs))
          (define (maybe-inline [ef : -e])
            (match ef
              [(-λ (? list? formals) bod)
               (cond
                 [(or (andmap arg-inlinable? xs*)
                      (for/and : Boolean ([x formals]) (<= (count-xs bod x) 1)))
                  (go (e/list (map -x formals) xs* bod))]
                 [else ; default to `let`
                  (-let-values
                   (for/list : (Listof (Pairof (Listof Symbol) -e)) ([x formals] [ex xs*])
                     (cons (list x) ex))
                   (go bod)
                   'havoc)])]
              [_ (-@ (go ef) xs* loc)]))

          (define (cases [f : -•] [x : -e]) : -e
            (define k→v
              (hash->list
               (for/fold ([acc : (HashTable -v -e) (hash)]) ([(k v) mappings])
                 (match k
                   [(-@ (≡ f) (list ek) _)
                    (define k
                      (cond
                        [(-v? ek) ek]
                        [(hash-ref mappings ek #f) => -b]
                        [else (error 'cases "unexpected ~a" (show-e ek))]))
                    (hash-set acc k (-b v))]
                   [_ acc]))))
            (match k→v
              ['() (-b 0)]
              [(cons (cons k₀ v₀) kvs)
               (foldr
                (λ ([p : (Pairof -v -e)] [acc : -e])
                  (-if (-@ 'equal? (list x (car p)) -Λ) (cdr p) acc))
                v₀
                kvs)]))

          (match f
            [(? -•? v)
             (cond [(concretized? Γ v) => maybe-inline]
                   [(equal? '✓ (Γ⊢e Γ (-?@ 'δ-case? v))) (cases v (car xs*))]
                   [else (-begin/simp xs*)])]
            [_ (maybe-inline f)])]
         [(-if e₀ e₁ e₂)
          (case (Γ⊢e Γ e₀)
            [(✓) (go e₁)]
            [(X) (go e₂)]
            [else (-if (go e₀) (go e₁) (go e₂))])]
         [(-wcm k v b) (-wcm (go k) (go v) (go b))]
         [(-begin es) (-begin (map go es))]
         [(-begin0 e₀ es) (-begin0 (go e₀) (map go es))]
         [(-let-values bnds bod ctx)
          (-let-values
           (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             (cons xs (go ex)))
           (go bod)
           ctx)]
         [(-letrec-values bnds bod ctx)
          (-letrec-values
           (for/list : (Listof (Pairof (Listof Symbol) -e)) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             (cons xs (go ex)))
           (go bod)
           ctx)]
         [(-set! x e*) (-set! x (go e*))]
         [(-μ/c x c) (-μ/c x (go c))]
         [(-->i doms rst rng pos)
          (-->i
           (for/list : (Listof (Pairof Symbol -e)) ([dom doms])
             (match-define (cons x c) dom)
             (cons x (go c)))
           (match rst
             [(cons x* c*) (cons x* (go c*))]
             [#f #f])
           (go rng)
           pos)]
         [(-struct/c si cs pos) (-struct/c si (map go cs) pos)]
         [e e])])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct exn:fail:gen exn:fail ([predicate : -o] [v : -e] [Γ : -Γ]) #:transparent)

(define-syntax try-gen
  (syntax-rules ()
    [(_ e) e]
    [(_ e₀ e ...)
     (with-handlers ([exn:fail:gen?
                      (λ (_) (try-gen e ...))])
       e₀)]))

(: blind-guess : -Γ (HashTable -e Base) -e → -e)
;; Attempt to instantiate value at opaque location `ℓ` as long as it doesn't violate
;; path invariant and other instantiated values in `mappings`
(define (blind-guess Γ mappings e•)

  (begin
    (dbg 'inst "guess: ~a~n" (show-e e•)))
  

  (define-syntax-rule (fail-gen o v)
    (raise (exn:fail:gen "Fail to generate concrete value" (current-continuation-marks) o v Γ)))

  ;; Make sure concrete value doesn't contradict path invariant
  (define (guard [v• : -e] [b : -b]) : (Option -b)
    (and (for/and : Boolean ([φ (-Γ-facts Γ)])
           (not (equal? 'X (Γ⊢e -Γ⊤ (e/ v• b φ)))))
         b))

  (define (try-val [v• : -e] [b : Base] [l : Symbol])
    (cond [(guard v• (-b b)) => -b-unboxed]
          [else (fail-gen l v•)]))

  (define (gen-integer [v• : -e])
    (-b
     (or (for/or : (Option Integer) ([i 10])
           (and (guard v• (-b i)) i))
         (fail-gen 'integer? v•))))

  (define (gen-rational [v• : -e])
    (try-gen
     (gen-integer v•)
     (-b ; TR doens't like `for*/or` :(
      (or (for/or : (Option Exact-Rational) ([d (in-range 0 20)])
            (for/or : (Option Exact-Rational) ([n (in-range 2 20)])
              (define q (/ d n))
              (and (guard v• (-b q)) q)))
          (fail-gen 'rational? v•)))))

  (define (gen-real [v• : -e])
    (try-gen
     (gen-integer v•)
     (gen-rational v•)
     (-b
      (or (for/or : (Option Real) ([b 10])
            (for/or : (Option Real) ([_ 10])
              (define r (random))
              (and (guard v• (-b r)) r)))
          (try-val v• +inf.0 'real?)
          (try-val v• -inf.0 'real?)
          (fail-gen 'real? v•)))))

  (define (gen-number [v• : -e])
    (define (rand-rat) (exact->inexact (/ (+ 1 (random 999)) 1000)))
    (try-gen
     (gen-integer v•)
     (gen-rational v•)
     (gen-real v•)
     (-b
      (or (for/or : (Option Number) ([_ 100])
            (define c (make-rectangular (rand-rat) (rand-rat)))
            (and (guard v• (-b c)) c))
          (fail-gen 'number? v•)))))

  (define (gen-symbol [v• : -e])
    (-b
     (or (for/or : (Option Symbol) ([i 100])
           (string->symbol (format "symbol_~a" i)))
         (fail-gen 'symbol? v•))))

  (: gen-string ([-e] [(Option Natural)] . ->* . -b))
  (define (gen-string v• [len #f])
    (cond
      [len
       (define pool
         "ABCDEFGHIJKLMNOPQRSTUVWXYZabcedfghijklmnopqrstuvwxyz0123456789 ,./<>?;:{}~!@#$%^&*()♥◆♣♠")
       (define pool-len (string-length pool))
       (-b (or (for/or : (Option String) ([_ 100])
                 (define s
                   (list->string (for/list : (Listof Char) ([_ len])
                                   (string-ref pool (random pool-len)))))
                 (and (guard v• (-b s)) s))
               (fail-gen 'string? v•)))]
      [(hash-ref mappings (assert (-?@ 'string-length v•)) #f) =>
       (λ ([n : Base])
         (gen-string v• (assert n exact-nonnegative-integer?)))]
      [else
       (try-gen
        (gen-string v• 0)
        (gen-string v• 1)
        (gen-string v• 2)
        (gen-string v• 3)
        (gen-string v• 4)
        (gen-string v• 5)
        (gen-string v• 6)
        (fail-gen 'string? v•))]))

  (define (gen-procedure [v• : -e])
    (define arities
      (for/fold ([arities : (Setof Natural) ∅]) ([φ (-Γ-facts Γ)])
        (match φ
          [(-@ (or '= 'equal? 'arity-includes?)
               (list (-@ 'procedure-arity (list (≡ v•)) _)
                     (-b (? exact-nonnegative-integer? n)))
               _)
           (set-add arities n)]
          [_ arities])))
    (match (set->list arities)
      [(list) (-λ '() -tt)]
      [(list n)
       (-λ (build-list n (λ ([i : Integer]) (string->symbol (format "x~a" (n-sub i))))) -tt)]
      [_ (-λ (-varargs '() 'args) -tt)]))
  
  (define (gen-non-false [v• : -e])
    (or (guard v• -tt)
        (try-gen
         (gen-number v•)
         (gen-symbol v•)
         (gen-string v•)
         (fail-gen 'values v•))))

  (define (gen-any [v• : -e]) : (U -b -@)
    (try-gen
     (if (guard v• -ff) -ff (gen-non-false v•))
     (fail-gen 'any/c v•)))

  (match (most-specific-pred Γ e•)
    [(? symbol? o)
     (case o
       [(not) -ff]
       [(null?) -null]
       [(void?) (-b (void))]
       [(zero?) (-b 0)]
       [(integer?) (gen-integer e•)]
       [(rational? real?) (gen-real e•)]
       [(number?) (gen-number e•)]
       [(symbol?) (gen-symbol e•)]
       [(string?) (gen-string e•)]
       [(procedure?) (gen-procedure e•)]
       [(values) (gen-non-false e•)]
       [(any/c) (gen-any e•)]
       [else (error 'blind-guess "unhandled predicate ~a" o)])]
    [(-st-p s)
     (-@ (-st-mk s)
         (for/list : (Listof -e) ([fld (-struct-split e• s)])
           (cond
             [(and fld (hash-ref mappings fld #f)) => -b]
             [fld (blind-guess Γ mappings fld)]
             [else #|no constraint|# -tt]))
         -Λ)]))

;; See if it's ok to inline the application
(define (arg-inlinable? [e : -e])
  (or (-x? e) (-ref? e) (-prim? e)))
