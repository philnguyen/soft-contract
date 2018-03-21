#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         (only-in z3/ffi toggle-warning-messages!)
         typed/racket/unit
         z3/smt
         set-extras
         unreachable
         "../utils/main.rkt"
         "../ast/signatures.rkt"
         "../runtime/signatures.rkt"
         "signatures.rkt")

(define-unit ext-prover-core@
  (import)
  (export ext-prover-core^)

  (: check : Σ Φ V (Listof V) → Valid)
  (define (check Σ Φ^ P Vs) ???))

#|
(: should-call-smt? : -Γ -h (Listof -V) → Boolean)
  ;; Heuristic avoiding calling out to solvers
  ;; However this heuristic is implemented should be safe in terms of soundness.
  ;; Not calling out to solver when should only hurts precision.
  ;; Calling out to solver when there's no need only hurts performance.
  ;; TODO: re-inspect this after recent rewrite
  (define should-call-smt?
    (let ([difficult?
           (match-λ?
            '< '> '<= '>= '= 'zero?
            (? -</c?) (? ->/c?) (? -≤/c?) (? -≥/c?))])
      (λ (Γ h Vs)
        (and
         (difficult? h)
         (for/or : Boolean ([hs (in-hash-values Γ)]) ; TODO TR can't for*/or
           (for/or : Boolean ([h (in-set hs)])
             (difficult? h)))))))
|#

#|
(define-type (M T) (→ T))

(define-unit external-prover@
  (import static-info^ for-gc^ pretty-print^ path^ sto^ prims^)
  (export external-prover^)

  (: p∋V : -Γ -h (Listof -V) → -R)
  (define (p∋V Γ p Vs)
    #;(define (set-default-options!)
        (set-options! #:timeout 1000
                      #:mbqi? #t
                      #:macro-finder? #t
                      #:rlimit 400mv 0000))

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
    (define-values (tgt    env₁) (⦃t@⦄ Γ p ts (hasheq)))
    (define-values (do-bse env₂) (⦃Γ⦄ (span Γ (t-names (-t.@ p ts))) env₁))
    (define do-decl
      (λ ()
        (for ([(x t) (in-hash env₂)])
          (dynamic-declare-const x (t)))
        (for ([ast (in-list do-bse)])
          (assert! (ast)))))
    (values do-decl tgt))

  (: ⦃t@⦄ : -Γ -o (Listof -t) Env → (Values (M Z3-Ast) Env))
  (define (⦃t@⦄ Γ h ts env)
    (case h
      [(< <= > >= =)
       (define o
         (case h
           [(<) </s]
           [(<=) <=/s]
           [(>) >/s]
           [(>=) >=/s]
           [(=) =/s]))
       (match-define-values ((list ⦃t₁⦄ ⦃t₂⦄) env*) (⦃ts⦄ Γ ts env))
       (values (λ () (o (⦃t₁⦄) (⦃t₂⦄))) env*)]
      [(zero?)
       (define-values (⦃t⦄₁ env*) (⦃t⦄ Γ (car ts) env))
       (values (λ () (=/s (⦃t⦄₁) 0)) env*)]
      [(+ - *)
       (define o
         (case h
           [(+) +/s]
           [(-) -/s]
           [(*) */s]))
       (define-values (do-args env*) (⦃ts⦄ Γ ts env))
       (values (λ () (apply o ((list-M do-args)))) env*)]
      [(add1)
       (define-values (⦃t⦄₁ env*) (⦃t⦄ Γ (car ts) env))
       (values (λ () (+/s (⦃t⦄₁) 1)) env*)]
      [(sub1)
       (define-values (⦃t⦄₁ env*) (⦃t⦄ Γ (car ts) env))
       (values (λ () (-/s (⦃t⦄₁) 1)) env*)]
      [(not)
       (define-values (⦃t⦄₁ env*) (⦃t⦄ Γ (car ts) env))
       (values (λ () (not/s (⦃t⦄₁))) env*)]
      [else
       (define x (gen-name/memo (-t.@ h ts) #:tag 'exi))
       (define T (get-type Γ (-t.@ h ts)))
       (values (λ () (val-of x)) (hash-set env x (⦃T⦄ T)))]))

  (: ⦃prop⦄ : -Γ -h -t Env → (Values (M Z3-Ast) Env))
  (define (⦃prop⦄ Γ h t env)
    (match h
      [(-not/c o)
       (define-values (⦃t⦄* env*) (⦃prop⦄ Γ o t env))
       (values (λ () (not/s (⦃t⦄*))) env*)]
      [(-</c t*) (⦃t@⦄ Γ '<  (list t t*) env)]
      [(-≤/c t*) (⦃t@⦄ Γ '<= (list t t*) env)]
      [(->/c t*) (⦃t@⦄ Γ '>  (list t t*) env)]
      [(-≥/c t*) (⦃t@⦄ Γ '>= (list t t*) env)]
      [(-≡/c t*) (⦃t@⦄ Γ '=  (list t t*) env)]
      [(? -arity-includes/c?) (values (λ () true/s) env)]
      [(? -o? o) (⦃t@⦄ Γ o (list t) env)]))

  (: ⦃Γ⦄ : -Γ Env → (Values (Listof (M Z3-Ast)) Env))
  (define (⦃Γ⦄ Γ env)
    (for*/fold ([assertions : (Listof (M Z3-Ast)) '()] [env : Env env])
               ([(t ps) (in-hash Γ)]
                [p (in-set ps)])
      (define-values (asst env*) (⦃prop⦄ Γ p t env))
      (values (cons asst assertions) env*)))

  (: ⦃t⦄ : -Γ -t Env → (Values (M Z3-Ast) Env))
  (define (⦃t⦄ Γ t env)
    (match t
      [(? exact-integer? x)
       (define z (⦃x⦄ x))
       (values (λ () (val-of z)) (hash-set env z (⦃T⦄ (get-type Γ x))))]
      [(-b b) (values (⦃b⦄ b) env)]
      [(-t.@ o ts) (⦃t@⦄ Γ o ts env)]))

  (: ⦃ts⦄ : -Γ (Listof -t) Env → (Values (Listof (M Z3-Ast)) Env))
  (define (⦃ts⦄ Γ ts env)
    (define-values (⦃ts⦄-rev env*)
      (for/fold ([⦃ts⦄-rev : (Listof (M Z3-Ast)) '()] [env : Env env])
                ([tᵢ (in-list ts)])
        (define-values (⦃t⦄ᵢ env*) (⦃t⦄ Γ tᵢ env))
        (values (cons ⦃t⦄ᵢ ⦃ts⦄-rev) env*)))
    (values (reverse ⦃ts⦄-rev) env*))

  (: ⦃b⦄ : Base → (M Z3-Ast))
  (define ⦃b⦄
    (match-lambda
      [(? exact-integer? b)
       (λ () (mk-numeral (get-context) (number->string b) Int/s))]
      [(? real? b)
       (λ () (mk-numeral (get-context) (number->string b) Real/s))]
      [b (error '⦃b⦄ "unsupported base value: ~a of ~a" b)]))

  (: ⦃x⦄ : Integer → Symbol)
  (define (⦃x⦄ x) (format-symbol "x-~a" x))

  (: get-type : -Γ -t → Type)
  (define (get-type Γ t)
    (or (let go : (Option Type) ([t : -t t])
          (match (hash-ref Γ t #f)
            [(? set? ps)
             (cond
               [(not (set-empty? (∩ ps {set 'integer? 'exact-integer? 'exact-nonnegative-integer? 'exact-positive-integer?})))
                'Int]
               [(not (set-empty? (∩ ps {set 'real? 'inexact-real? 'float?})))
                'Real]
               [(not (set-empty? (∩ ps {set 'not 'boolean?})))
                'Bool]
               [else #f])]
            [#f
             (match t
               [(-t.@ (or 'add1 'sub1 '+ '- '*) ts) (or (ormap go ts) 'Real)]
               [(-t.@ '/ _) 'Real]
               [(-t.@ (? -st-p?) _) 'Bool]
               [(-t.@ (-not/c _) _) 'Bool]
               [(-t.@ (? symbol? o) _)
                (case (get-conservative-range o)
                  [(boolean?) 'Bool]
                  [(integer? exact-integer? exact-nonnegative-integer? exact-positive-integer?) 'Int]
                  [(real? inexact-real?) 'Real]
                  [else #f])]
               [_ #f])]))
        (error 'get-type "cannot determine ~a's type in ~a" (show-t t) (show-Γ Γ))))

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
             (for*/unioneq : (℘ Integer) ([t (in-hash-keys Γ)])
               (set-subtract (t-names t) all*)))
           (loop front* all*)])))
    (for/fold ([Γ : -Γ Γ])
              ([t (in-hash-keys Γ)]
               #:when (set-empty? (set-intersect (t-names t) dom*)))
      (hash-remove Γ t)))

  (: gen-name/memo ([-t] [#:tag Symbol] . ->* . Symbol))
  (define gen-name/memo
    (let ([m : (HashTable (Pairof Symbol -t) Symbol) (make-hash)])
      (λ ([t : -t] #:tag [tag 'exi])
        (hash-ref! m (cons tag t) (λ () (gensym (format-symbol "~a-" tag)))))))

  
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
|#
