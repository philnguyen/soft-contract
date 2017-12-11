#lang typed/racket/base

(provide external-prover@)

(require racket/match
         racket/set
         racket/list
         racket/splicing
         (only-in z3/ffi toggle-warning-messages!)
         typed/racket/unit
         z3/smt
         bnf
         intern
         set-extras
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt"
         "../signatures.rkt")

(define-type (M T) (→ T))

(define-unit external-prover@
  (import static-info^ for-gc^ pretty-print^ path^ sto^)
  (export external-prover^)

  (: p∋V : -Γ -h (Listof -V) → -R)
  (define (p∋V Γ p Vs)
    #;(define (set-default-options!)
        (set-options! #:timeout 1000
                      #:mbqi? #t
                      #:macro-finder? #t
                      #:rlimit 4000000))

    (cond
      [(and (handled-pred? p) (andmap -t? Vs))
       (define-values (do-base do-target) (translate Γ p Vs))
       (case (run (do do-base
                      (λ () (assert! (do-target)))
                      check-sat))
         [(unsat) '✗]
         [(sat unknown)
          (case (run (do do-base
                         (λ () (assert-not! (do-target)))
                         check-sat))
            [(unsat) '✓]
            [(sat unknown) '?])])]
      [else '?]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Translate
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-type Handled-Pred (U '< '<= '> '>= '= 'equal? 'zero?))
  (define-predicate handled-pred? Handled-Pred)
  (define-type Env (HashTable Symbol (M Smt-Sort-Expr)))
  (define-type Type (U 'Int 'Real 'Bool))

  (: translate : -Γ Handled-Pred (Listof -t) → (Values (M Void) (M Z3-Ast)))
  (define (translate Γ p ts)
    (define-values (tgt    env₁) (⦃t@⦄ p ts 'Bool (hasheq)))
    (define-values (do-bse env₂) (⦃Γ⦄ (span Γ (t-names (-t.@ p ts))) env₁))
    (define do-decl
      (λ ()
        (for ([(x t) (in-hash env₂)])
          (dynamic-declare-const x (t)))
        (for ([ast (in-list do-bse)])
          (assert! (ast)))))
    (values do-decl tgt))

  (: ⦃t@⦄ : -h (Listof -t) Type Env → (Values (M Z3-Ast) Env))
  (define (⦃t@⦄ h ts T env)
    (case h
      [(< <= > >= =)
       (define o
         (case h
           [(<) </s]
           [(<=) <=/s]
           [(>) >/s]
           [(>=) >=/s]
           [(=) =/s]))
       (define Ts #|TODO|# (make-list (length ts) 'Real))
       (match-define-values ((list ⦃t₁⦄ ⦃t₂⦄) env*) (⦃ts⦄ ts Ts env))
       (values (λ () (o (⦃t₁⦄) (⦃t₂⦄))) env*)]
      [(+ - *)
       (define o
         (case h
           [(+) +/s]
           [(-) -/s]
           [(*) */s]))
       (define Ts #|TODO|# (make-list (length ts) 'Real))
       (match-define-values (do-args env*) (⦃ts⦄ ts Ts env))
       (values (λ () (apply o ((list-M do-args)))) env*)]
      [else
       (define x (gensym 'exi-))
       (values (λ () (val-of x)) (hash-set env x (⦃T⦄ T)))]))

  (: ⦃Γ⦄ : -Γ Env → (Values (Listof (M Z3-Ast)) Env))
  (define (⦃Γ⦄ Γ env)
    (for*/fold ([assertions : (Listof (M Z3-Ast)) '()] [env : Env env])
               ([(ts ps) (in-hash Γ)]
                [p (in-set ps)])
      (define T #|TODO|# 'Bool)
      (define-values (asst env*) (⦃t@⦄ p ts T env))
      (values (cons asst assertions) env*)))

  (: ⦃t⦄ : -t Type Env → (Values (M Z3-Ast) Env))
  (define (⦃t⦄ t T env)
    (match t
      [(? exact-integer? x)
       (define z (⦃x⦄ x))
       (values (λ () (val-of z)) (hash-set env z (⦃T⦄ T)))]
      [(-b b) (values (⦃b⦄ b T) env)]
      [(-t.@ o ts) (⦃t@⦄ o ts #|TODO|# 'Real env)]))

  (: ⦃ts⦄ : (Listof -t) (Listof Type) Env → (Values (Listof (M Z3-Ast)) Env))
  (define (⦃ts⦄ ts Ts env)
    (define-values (⦃ts⦄-rev env*)
      (for/fold ([⦃ts⦄-rev : (Listof (M Z3-Ast)) '()] [env : Env env])
                ([tᵢ (in-list ts)] [Tᵢ (in-list Ts)])
        (define-values (⦃t⦄ᵢ env*) (⦃t⦄ tᵢ Tᵢ env))
        (values (cons ⦃t⦄ᵢ ⦃ts⦄-rev) env*)))
    (values (reverse ⦃ts⦄-rev) env*))

  (: ⦃b⦄ : Base Type → (M Z3-Ast))
  (define (⦃b⦄ b t)
    (match* (t b)
      [('Int (? exact-integer? b))
       (λ () (mk-numeral (get-context) (number->string b) Int/s))]
      [('Real (? real? b))
       (λ () (mk-numeral (get-context) (number->string b) Real/s))]
      [(_ _)
       (error '⦃b⦄ "unsupported base value: ~a of ~a" b t)]))

  (: ⦃x⦄ : Integer → Symbol)
  (define (⦃x⦄ x) (format-symbol "x-~a" x))

  (define/memoeq (⦃T⦄ [T : Type]) : (M Smt-Sort-Expr)
    (case T
      [(Int)  (λ () Int/s)]
      [(Real) (λ () Real/s)]
      [(Bool) (λ () Bool/s)]))

  (: span : -Γ (℘ Integer) → -Γ)
  (define (span Γ dom)
    ;; FIXME horribly inefficient
    (define dom* : (℘ Integer)
      (let loop ([front : (℘ Integer) dom] [all : (℘ Integer) ∅eq])
        (cond
          [(set-empty? front) all]
          [else
           (define all* (∪ front all))
           (define front*
             (for*/unioneq : (℘ Integer) ([ts (in-hash-keys Γ)]
                                          [t (in-list ts)])
               (set-subtract (t-names t) all*)))
           (loop front* all*)])))
    (for/fold ([Γ : -Γ Γ])
              ([ts (in-hash-keys Γ)]
               #:when (set-empty? (set-intersect (t-names (-t.@ 'values ts)) dom*)))
      (hash-remove Γ ts)))

  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; For-Translate
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (: ret (∀ (α) α → (M α)))
  (define (ret v) (λ () v))

  (: >>= (∀ (α β) (M α) (α → (M β)) → (M β)))
  (define ((a . >>= . mb)) ((mb (a))))

  (define-syntax do
    (syntax-rules (← ≔ :)
      [(_ m) m]
      [(_ [p : τ ← m₁] m ...) (m₁ . >>= . (λ ([x : τ])
                                            (match-define p x)
                                            (do m ...)))]
      [(_ [p ≔ e ] m ...) (match-let ([p e]) (do m ...))]
      [(_  m₁      m ...) (m₁ . >>= . (λ _ (do m ...)))]))

  (: list-M (∀ (α) (Listof (M α)) → (M (Listof α))))
  (define ((list-M ms))
    (for/list : (Listof α) ([m (in-list ms)]) (m)))

  (: run (∀ (α) (M α) → α))
  (define (run m)
    (with-new-context (m)))

  (define (assert-not! [ψ : Z3-Ast]) (assert! (not/s ψ)))

  (toggle-warning-messages! #f))
