#lang typed/racket/base

(provide ext-prove ext-plausible-pc? Timeout)

(require racket/match
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "translate.rkt"
         "z3-rkt/z3-wrapper.rkt"
         "z3-rkt/parser.rkt"
         "z3-rkt/builtins.rkt"
         "z3-rkt/main.rkt")

(define-parameter Timeout : Nonnegative-Fixnum 500)
(Sat-Result . ::= . Z3:Sat-LBool 'timeout)
(toggle-warning-messages! #f)

(define (ext-prove [M : -M] [Γ : -Γ] [e : -e]) : -R
  ;(printf "ext-prove:~nM:~n~a~n~a ⊢ ~a~n~n" (show-M M) (show-Γ Γ) (show-e e))
  (match-define (cons base goal) (encode M Γ e))
  (match (exec-check-sat base goal)
    [(cons 'unsat _) '✓]
    [(cons _ 'unsat) '✗]
    [_ '?]))

(define (ext-plausible-pc? [M : -M] [Γ : -Γ]) : Boolean
  ;(printf "ext-plausible-pc?~nM:~n~a~nΓ:~n~a~n~n" (show-M M) (show-Γ Γ))
  (match-define (cons base _) (encode M Γ #|HACK|# -ff))
  (case (exec-check-sat₀ base)
    [(unsat) #f]
    [else #t]))

(define/memo (exec-check-sat₀ [asserts : (→ Void)]) : Z3:LBool
  (with-fresh-context (#:timeout (Timeout))
    (asserts)
    (check-sat))
  #;(with-fresh-solver
    (with-fresh-environment
      (asserts)
      (check-sat))))

(define/memo (exec-check-sat [asserts : (→ Void)] [goal : (→ Z3:Ast)]) : (Pairof Sat-Result Sat-Result)
  (with-fresh-context (#:timeout (Timeout))
    (asserts)
    (match (with-local-push-pop
             (assert! (@/s 'is_false (goal)))
             (check-sat))
      ['false (cons 'unsat 'unknown)]
      [a
       (cons (z3:lbool->sat-result a)
             (z3:lbool->sat-result
              (with-local-push-pop
                (assert! (@/s 'is_truish (goal)))
                (check-sat))))]))
  #;(with-fresh-solver
    (with-fresh-environment
      (asserts)
      (match (with-local-push-pop
              (assert! (@/s 'is_false (goal)))
              (check-sat))
        ['false (cons 'unsat 'unknown)]
        [a
         (cons (z3:lbool->sat-result a)
               (z3:lbool->sat-result
                (with-local-push-pop
                 (assert! (@/s 'is_truish (goal)))
                 (check-sat))))]))))

(: z3:lbool->sat-result : Z3:LBool → Sat-Result)
(define (z3:lbool->sat-result x)
  (case x
    [(false) 'unsat]
    [(true) 'sat]
    [else 'unknown]))
