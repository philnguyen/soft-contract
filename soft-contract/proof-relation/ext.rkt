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

(: ext-prove : -M -Γ -e → -R)
(define (ext-prove M Γ e)
  (define-values (base goal) (encode M Γ e))
  (match/values (check-sat base goal)
    [('unsat _) '✓]
    [(_ 'unsat) '✗]
    [(_ _) '?]))

(: ext-plausible-pc? : -M -Γ → Boolean)
(define (ext-plausible-pc? M Γ)
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
