#lang typed/racket/base

(provide ext-prove ext-plausible-pc?)

(require racket/match
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "translate.rkt"
         "parameters.rkt"
         "z3-rkt/z3-wrapper.rkt"
         "z3-rkt/parser.rkt"
         "z3-rkt/builtins.rkt"
         "z3-rkt/main.rkt")

(define/memo (ext-prove [M : -M] [Γ : -Γ] [e : -e]) : -R
  ;(printf "ext-prove:~nM:~n~a~n~a ⊢ ~a~n~n" (show-M M) (show-Γ Γ) (show-e e))
  (define-values (base goal) (encode M Γ e))
  (match/values (check-sat base goal)
    [('unsat _) '✓]
    [(_ 'unsat) '✗]
    [(_ _) '?]))

(define/memo (ext-plausible-pc? [M : -M] [Γ : -Γ]) : Boolean
  ;(printf "ext-plausible-pc?~nM:~n~a~nΓ:~n~a~n~n" (show-M M) (show-Γ Γ))
  (define-values (base _) (encode M Γ #|HACK|# -ff))

  (case (smt:with-context (smt:new-context)
          (base)
          (smt:check-sat))
    [(unsat) #f]
    [else #t]))

(: check-sat : (→ Void) (→ Z3:Ast) → (Values Sat-Result Sat-Result))
(define (check-sat asserts goal)
  (match (smt:with-context (smt:new-context)
           (asserts)
           (smt:assert (@/s 'is_false (goal)))
           (smt:check-sat))
    ['unsat (values 'unsat 'unknown)]
    [r₁
     (values r₁
             (smt:with-context (smt:new-context)
               (asserts)
               (smt:assert (@/s 'is_truish (goal)))
               (smt:check-sat)))]))
