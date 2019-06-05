#lang typed/racket/base

(require racket/match
         racket/set
         racket/list
         racket/string
         racket/splicing
         racket/extflonum
         typed/racket/unit
         set-extras
         "../utils/main.rkt"
         "signatures.rkt"
         )

(provide ast-pretty-print@)
(define-unit ast-pretty-print@
  (import static-info^)
  (export ast-pretty-print^)

  (define (show-b [x : Base]) : Sexp
    (cond
      [(string? x) (format "\"~a\"" x)]
      [(or (symbol? x) (keyword? x)) `(quote ,x)]
      [(and (real? x) (inexact? x))
       (define s (number->string x))
       (substring s 0 (min (string-length s) 5))]
      [(or (regexp? x) (pregexp? x) (byte-regexp? x) (byte-pregexp? x) (bytes? x)) (format "~a" x)]
      [(extflonum? x) (extfl->inexact x)]
      [(void? x) 'void]
      [(arity-at-least? x) `(arity-at-least ,(arity-at-least-value x))]
      [(list? x) `(list ,@(map show-b x))]
      [(eof-object? x) '⟪eof⟫]
      [(path? x) (path->string x)]
      [(defined? x) x]
      [else 'undefined]))

  ;; Return operator's simple show-o for pretty-printing
  (define show-o : (-o → Symbol)
    (match-lambda
      [(? symbol? s) s]
      [(-st-mk 𝒾) (format-symbol "_~a" (-𝒾-name 𝒾))]
      [(-st-ac 𝒾 i) (format-symbol "_~a" (struct-accessor-name 𝒾 i))]
      [(-st-p 𝒾) (format-symbol "_~a?" (-𝒾-name 𝒾))]
      [(-st-mut (== -𝒾-mcons) 0) 'set-mcar!]
      [(-st-mut (== -𝒾-mcons) 1) 'set-mcdr!]
      [(-st-mut (== -𝒾-box) _) 'set-box!]
      [(-st-mut 𝒾 i) (format-symbol "set-~a._~a!" (-𝒾-name 𝒾) i)]))

  (define (show-e [e : -e]) : Sexp
    (match e
      ; syntactic sugar
      [(-λ (-var (list x) #f) (-@ 'not (list (-@ f (list (-x x _)) _)) _) _) `(not/c ,(show-e f))]
      [(-λ (-var (list x) #f) (-@ '= (list (-x x _) e*) _) _) `(=/c ,(show-e e*))]
      [(-λ (-var (list x) #f) (-@ (or 'equal? 'eq? 'eqv?) (list (-x x _) e*) _) _) `(≡/c ,(show-e e*))]
      [(-λ (-var (list x) #f) (-@ '> (list (-x x _) e*) _) _) `(>/c ,(show-e e*))]
      [(-λ (-var (list x) #f) (-@ '< (list (-x x _) e*) _) _) `(</c ,(show-e e*))]
      [(-λ (-var (list x) #f) (-@ '>= (list (-x x _) e*) _) _) `(≥/c ,(show-e e*))]
      [(-λ (-var (list x) #f) (-@ '<= (list (-x x _) e*) _) _) `(≤/c ,(show-e e*))]
      
      [(-if a b (-b #f) _)
       (match* ((show-e a) (show-e b))
         [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l (Listof Sexp)) ,@(cast r (Listof Sexp)))]
         [(`(and ,l ...) r) `(and ,@(cast l (Listof Sexp)) ,r)]
         [(l `(and ,r ...)) `(and ,l ,@(cast r (Listof Sexp)))]
         [(l r) `(and ,l ,r)])]
      [(-if a b (-b #t) _) `(implies ,(show-e a) ,(show-e b))]

      [(-λ xs e _) `(λ ,(show-formals xs) ,(show-e e))]
      [(-case-λ cases _)
       `(case-lambda
          ,@(for/list : (Listof Sexp) ([c (in-list cases)])
              (match-define (-λ (-var xs ?z) e _) c)
              (if ?z
                  `[,(cons xs ?z) ,(show-e e)]
                  `[,xs ,(show-e e)])))]
      [(-•) '•]
      [(-b b) (show-b b)]
      [(? -o? o) (show-o o)]
      [(-x x _) (if (symbol? x) x (-𝒾-name x))]
      [(-let-values bnds body _)
       (match bnds
         [(list (cons (list lhs) rhs) ...)
          `(let ,(for/list : (Listof Sexp) ([x (in-list lhs)]
                                            [e (in-list rhs)])
                   `(,(assert x symbol?) ,(show-e (assert e -e?))))
             ,(show-e body))]
         [_
          `(let-values
               ,(for/list : (Listof Sexp) ([bnd bnds])
                  (match-define (cons xs ex) bnd)
                  `(,xs ,(show-e ex)))
             ,(show-e body))])]
      [(-letrec-values bnds body _)
       (match bnds
         [(list (cons (list lhs) rhs) ...)
          `(letrec ,(for/list : (Listof Sexp) ([x (in-list lhs)]
                                               [e (in-list rhs)])
                      `(,(assert x symbol?) ,(show-e (assert e -e?))))
             ,(show-e body))]
         [_
          `(letrec-values
               ,(for/list : (Listof Sexp) ([bnd bnds])
                  (match-define (cons xs ex) bnd)
                  `(,xs ,(show-e ex)))
             ,(show-e body))])]
      [(-set! x e _) `(set! ,(if (symbol? x) x (-𝒾-name x)) ,(show-e e))]
      [(-@ f xs _) `(,(show-e f) ,@(show-es xs))]
      [(-begin es) `(begin ,@(show-es es))]
      [(-begin0 e es) `(begin0 ,(show-e e) ,@(show-es es))]
      [(-error msg _) `(error ,msg)]
      #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
      [(-if i t e _) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
      [(-μ/c x c) `(μ/c (,x) ,(show-e c))]
      [(-->i (-var cs c) d)
       `(->i ,@(map show-dom cs)
             ,@(if c `(#:rest ,(show-dom c)) '())
             ,(match d
                [#f 'any]
                [(list d) (show-dom d)]
                [(? values ds) `(values ,@(map show-dom ds))]))]
      [(case--> cases) `(case-> ,@(map show-e cases))]
      [(-x/c.tmp x) x]
      [(-∀/c xs c _) `(parametric->/c ,xs ,(show-e c))]))

  (: show-dom : -dom → Sexp)
  (define show-dom
    (match-lambda
      [(-dom x ?xs d _)
       (if ?xs `(,x ,?xs ,(show-e d)) `(,x ,(show-e d)))]))

  (define (show-es [es : (Sequenceof -e)]) : (Listof Sexp)
    (for/list ([e es]) (show-e e)))

  (define (show-module [m : -module]) : (Listof Sexp)
    (match-define (-module path forms) m)
    `(module ,path scv:lang
       ,@(map show-module-level-form forms)))

  (define show-module-level-form : (-module-level-form → Sexp)
    (match-lambda
      [(-provide specs) `(provide ,@(map show-provide-spec specs))]
      [(? -general-top-level-form? m) (show-general-top-level-form m)]
      [(? -module? m) (show-module m)]))

  (define show-general-top-level-form : (-general-top-level-form → Sexp)
    (match-lambda
      [(? -e? e) (show-e e)]
      [(-define-values xs e _)
       (match* (xs e)
         [((list f) (-λ xs e* _)) `(define (,f ,@(show-formals xs)) ,(show-e e*))]
         [((list x) _) `(define ,x ,(show-e e))]
         [(_ _) `(define-values ,xs ,(show-e e))])]
      [(-require specs) `(require ,@(map show-require-spec specs))]))

  (define show-provide-spec : (-provide-spec → Sexp)
    (match-lambda
      [(-p/c-item x c _) `(,x ,(show-e c))]
      [(? symbol? x) x]))

  (define show-require-spec : (-require-spec → Sexp)
    values)

  (define show-formals : (-formals → Sexp)
    (match-lambda
      [(-var xs (? values x)) (cons xs x)]
      [(-var xs _) xs]))

  (define show-𝒾 : (-𝒾 → Symbol)
    (match-lambda
      [(-𝒾 name from) (format-symbol "~a@~a" name from)]))

  (: show-values-lift (∀ (X) (X → Sexp) → (Listof X) → Sexp))
  (define (show-values-lift show-elem)
    (match-lambda
      [(list x) (show-elem x)]
      [xs `(values ,@(map show-elem xs))]))

  (define show-values (show-values-lift show-e))

  (define (show-subst [m : Subst]) : (Listof Sexp)
    (for/list ([(k v) m]) `(,k ↦ ,(show-e v))))
  )
