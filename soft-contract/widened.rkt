#lang typed/racket/base

(provide (all-defined-out)) ; TODO

(require
 racket/match racket/set racket/list racket/bool racket/function racket/format
 "utils/set.rkt" "utils/map.rkt" "utils/untyped-macros.rkt" "utils/debug.rkt" "utils/pretty.rkt"
 "ast/definition.rkt"
 "runtime/path-inv.rkt" "runtime/val.rkt" "runtime/summ.rkt" "runtime/store.rkt"
 "reduction/main.rkt"
 "proof-relation/main.rkt" "proof-relation/local.rkt" "proof-relation/ext/query-z3.rkt"
 "machine.rkt")
(require/typed "parse.rkt"
  [files->prog ((Listof Path-String) → -prog)]
  [init-prim (Listof -module-level-form)])

(define-type -tσ Integer)
(define-type -tΞ Integer)
(define-type -t (Pairof -tσ -tΞ))
(define -t₀ : -t (cons 0 0))

;; Check whether `t₁` subsumes `t₂`
(define (t>= [t₁ : -t] [t₂ : -t]) : Boolean
  (match-define (cons x₁ y₁) t₁)
  (match-define (cons x₂ y₂) t₂)
  (and (>= x₁ x₂) (>= y₁ y₂)))

;; configuration
(struct -Cfg ([e : -E] [Γ : -Γ] [κ : -κ]) #:transparent)

(: Cfg-final? : -Cfg -Ξ → Boolean)
(define (Cfg-final? C Ξ)
  (match-define (-Cfg E _ κ) C)
  (final? E κ Ξ))

(define (show-Cfg [C : -Cfg]) : (Listof Sexp)
  (match-define (-Cfg E Γ κ) C)
  `((E: ,@(show-E E))
    (Γ: ,@(show-Γ Γ))
    (κ: ,@(show-κ κ))))

(define (show-S [S : (Map -Cfg -t)]) : (Listof Sexp)
  (for/list : (Listof Sexp) ([(C t) S])
    `(,@(show-Cfg C) ↦ ,t)))

;; For debugging only
(begin
  (define evals : (Map Integer (List (Map -Cfg -t) (Setof -Cfg) -σ -Ξ -M)) (make-hasheq))
  (define debug? : Boolean #f))

(: run : -prog → (Values (Map -Cfg -t) (Setof -Cfg) -σ -Ξ -M))
(define (run p)
  (match-define (-ς E₀ Γ₀ κ₀ σ₀ Ξ₀ M₀) (𝑰 p init-prim))
  (define C₀ (-Cfg E₀ Γ₀ κ₀))

  (: step : (Map -Cfg -t) (Setof -Cfg) -tσ -σ -tΞ -Ξ -M →
            (Values (Map -Cfg -t) (Setof -Cfg) -tσ -σ -tΞ -Ξ -M))
  (define (step S F tσ σ tΞ Ξ M)

    ;; for debugging only
    (hash-set! evals (hash-count evals) (list S F σ Ξ M))
    (when debug? ; debuggings
      (printf "Step: ~a: ~a~n" (hash-count evals) (set-count F))
      (for ([C F])
        (match-define (-Cfg E Γ κ) C)
        (printf "  E: ~a~n"   (show-E E))
        (printf "  Γ: ~a~n" (show-Γ Γ))
        (printf "  κ: ~a~n~n" (show-κ κ)))
      (case (read)
        [(done) (error "done")]
        [(skip) (set! debug? #f)]
        [else (void)]))

    ; Intermediate new (narrow) states
    (define I
      (for/fold ([I : (Setof -Δς) ∅]) ([Cfg F])
        (match-define (-Cfg E Γ κ) Cfg)
        (match (↦ (-ς E Γ κ σ Ξ M))
          [(? set? s) (∪ I s)]
          [(? -Δς? ς) (set-add I ς)])))

    ; Updated shared widened stores
    (define-values (σ* Ξ* M* δσ? δΞ?)
      (for/fold ([σ* : -σ σ] [Ξ* : -Ξ Ξ] [M* : -M M] [δσ? : Boolean #f] [δΞ? : Boolean #f])
                ([ςi I])
        (match-define (-Δς _ _ _ δσi δΞi δMi) ςi)
        (define-values (σ** δσi?) (Δ+ δσi σ*))
        (define-values (Ξ** δΞi?) (Δ+ δΞi Ξ*))
        (define-values (M** _   ) (Δ+ δMi M*))
        (values σ** Ξ** M** (or δσ? δσi?) (or δΞ? δΞi?))))
    (define tσ* (if δσ? (+ 1 tσ) tσ))
    (define tΞ* (if δΞ? (+ 1 tΞ) tΞ))

    ; Next frontier and updated seen states
    (define-values (F* S*)
      (for/fold ([F* : (Setof -Cfg) ∅] [S* : (Map -Cfg -t) S]) ([ςi I])
        (match-define (-Δς Ei Γi κi _ _ _) ςi)
        (define Ci (-Cfg Ei Γi κi))
        (define ti (hash-ref S* Ci #f))
        (define t* (cons tσ* tΞ*))
        (cond [(and ti (t>= ti t*)) (values F* S*)]
              [else (values (set-add F* Ci) (hash-set S* Ci t*))])))
    
    (values S* F* tσ* σ* tΞ* Ξ* M*))

  (let go : (Values (Map -Cfg -t) (Setof -Cfg) -σ -Ξ -M)
       ([S : (Map -Cfg -t) (hash C₀ -t₀)]
        [F : (Setof -Cfg) {set C₀}]
        [tσ : -tσ 0]
        [σ : -σ σ₀]
        [tΞ : -tΞ 0]
        [Ξ : -Ξ Ξ₀]
        [M : -M M₀])
    (define-values (S* F* tσ* σ* tΞ* Ξ* M*) (step S F tσ σ tΞ Ξ M))
    (cond
      [(set-empty? F*)
       (define A*
         (for/set: : (Setof -Cfg) ([Cfg (in-hash-keys S)]
                                   #:when (Cfg-final? Cfg Ξ*)
                                   #:unless (match? Cfg (-Cfg (-blm (or 'Λ '†) _ _ _) _ _)))
           Cfg))
       (values S* A* σ* Ξ* M*)]
      [else (go S* F* tσ* σ* tΞ* Ξ* M*)])))

(: run-files : Path-String * → (Values (Map -Cfg -t) (Setof -Cfg) -σ -Ξ -M))
(define (run-files . paths)
  (run (files->prog paths)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Debugging
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require/typed profile
    [profile-thunk ([(→ Void)] [#:delay Real #:repeat Integer] . ->* . Void)])

  (define-syntax-rule (profile* e ...)
    #;(begin
        (collect-garbage) (collect-garbage) (collect-garbage)
        (profile-thunk (λ () e ...) #:delay 0.0001 #:repeat 5))
    (begin (collect-garbage) (collect-garbage) (collect-garbage) e ...))

  (profile*

   (define t₁ (current-milliseconds))
   (define-values (S* A* σ* Ξ* M*)
     (parameterize ([debugs {set}]
                    [Γ⊢₀ Γ⊢e]
                    [Γ⊢ₑₓₜ z3⊢])
       (run (files->prog (list "test/programs/safe/2.rkt")))))
   (define t₂ (current-milliseconds))
   (begin ; debuggings
     (printf "Time: ~a~n" (~r (exact->inexact (/ (- t₂ t₁) 1000)) #:precision 4))
     (printf "|S| = ~a~n" (hash-count S*))
     (printf "|Steps| = ~a~n" (hash-count evals))
     (printf "|σ| = ~a~n" (hash-count σ*))
     (printf "|Ξ| = ~a~n" (hash-count Ξ*))
     (printf "|M| = ~a~n" (hash-count M*))
     (printf "Answers:~n")
     (for ([Cfg A*])
       (match-define (-Cfg E Γ _) Cfg)
       (printf "  E: ~a~n" (show-E E))
       (printf "  Γ:")
       (for ([e (show-Γ Γ)]) (printf " ~a" e))
       (printf "~n~n")))
   

   (define (f [n : Integer]) : (Setof -Cfg)
     (match-define (list _ F _ _ _) (hash-ref evals n))
     F)

   (define (F [n : Integer])
     (for/list : (Listof Sexp) ([C (f n)])
       (show-Cfg C)))

   (define-values
     (SS σσ ΞΞ MM)
     (values
      (show-S S*)
      (show-σ σ*)
      (show-Ξ Ξ*)
      (show-M M*)))

   (define (fronts)
     (printf "Frontier sizes:~n")
     (for ([i (in-range (hash-count evals))])
       (match-define (list _ F _ _ _) (hash-ref evals i))
       (printf " |F~a| = ~a~n" (n-sub i) (set-count F))))
   
   (void)))
