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

(toggle-warning-messages! #f)

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

  (case (with-fresh-managed-context ()
          (base)
          (smt:check-sat))
    [(unsat) #f]
    [else #t]))

(: check-sat : (→ Void) (→ Z3:Ast) → (Values Sat-Result Sat-Result))
(define (check-sat asserts goal)
  (with-fresh-managed-context (#:timeout (Timeout))
    (asserts)
    (match (smt:with-local-push-pop
             (smt:assert! (@/s 'is_false (goal)))
             (smt:check-sat))
      ['false (values 'unsat 'unknown)]
      [a
       (values (z3:lbool->sat-result a)
               (z3:lbool->sat-result
                (smt:with-local-push-pop
                  (smt:assert! (@/s 'is_truish (goal)))
                  (smt:check-sat))))])))

(: z3:lbool->sat-result : Z3:LBool → Sat-Result)
(define (z3:lbool->sat-result x)
  (case x
    [(false) 'unsat]
    [(true) 'sat]
    [else 'unknown]))
