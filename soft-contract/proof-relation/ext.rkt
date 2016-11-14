#lang typed/racket/base

(provide ext-prove ext-plausible-pc? Timeout)

(require racket/match
         (only-in z3/ffi toggle-warning-messages!)
         z3/smt
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "translate.rkt")

(define-parameter Timeout : Nonnegative-Fixnum 200)
(Sat-Result . ::= . Smt-Sat 'timeout)
(toggle-warning-messages! #f)

(define (ext-prove [M : -M] [Γ : -Γ] [e : -e]) : -R
  #;(define t₀ (current-milliseconds))
  (with-debugging/off
    ((R)
     (match-define (cons base goal) (encode M Γ e))
     (match (exec-check-sat base goal)
       [(cons 'unsat _) '✓]
       [(cons _ 'unsat) '✗]
       [_ '?]))
    (define δt (- (current-milliseconds) t₀))
    (unless #f #;(< δt 300)
      (printf "ext-prove: ~a ⊢ ~a : ~a ~ams~n~n" (show-Γ Γ) (show-e e) R δt))))

(define (ext-plausible-pc? [M : -M] [Γ : -Γ]) : Boolean
  #;(define t₀ (current-milliseconds))
  (with-debugging/off
    ((plaus?)
     (match-define (cons base _) (encode M Γ #|HACK|# -ff))
     (case (exec-check-sat₀ base)
       [(unsat) #f]
       [(sat unknown) #t]))
    (define δt (- (current-milliseconds) t₀))
    (unless #f #;(< δt 300)
      (printf "ext-plausible? ~a : ~a ~ams~n~n" (show-Γ Γ) plaus? δt))))

(define (set-default-options!)
  (set-options! #:timeout (Timeout)
                #:mbqi? #t
                #:macro-finder? #t
                #:rlimit 4000000))

(define/memo (exec-check-sat₀ [asserts : (→ Void)]) : Smt-Sat
  (with-new-context
    (set-default-options!)
    (asserts)
    #;(check-sat/log 't0)
    (check-sat)))

(define/memo (exec-check-sat [asserts : (→ Void)] [goal : (→ Z3-Ast)]) : (Pairof Sat-Result Sat-Result)
  (match (with-new-context
           (set-default-options!)
           (asserts)
           (assert! (@/s 'is_false (goal)))
           (check-sat))
    ['false (cons 'unsat 'unknown)]
    [a
     (cons a
           (with-new-context
             (set-default-options!)
             (asserts)
             (assert! (@/s 'is_truish (goal)))
             (check-sat)))])
  ;; The incremental solver eats up memory and freezes my computer if query has `is_int`
  #;(with-new-context
    (set-default-options!)
    (asserts)
    (match (with-local-stack
             (assert! (@/s 'is_false (goal)))
             #;(check-sat/log 't1)
             (check-sat))
      ['false (cons 'unsat 'unknown)]
      [a
       (cons a
             (with-local-stack
               (assert! (@/s 'is_truish (goal)))
               #;(check-sat/log 't2)
               (check-sat)))])))

(: check-sat/log : Symbol → Smt-Sat)
;; Log all queries that take 2/3 Timeout or more
(define (check-sat/log tag)
  #;(begin
    (printf "check-sat:~n")
    (print-current-assertions)
    (printf "~n"))
  (define-values (reses t₁ t₂ t₃) (time-apply check-sat '()))
  (define res (car reses))
  #;(when (> t₁ (* (quotient (Timeout) 5) 4))
    (printf "check-sat: ~a ~a ~a~n" tag res t₁)
    (print-current-assertions)
    (printf "~n"))
  res)
