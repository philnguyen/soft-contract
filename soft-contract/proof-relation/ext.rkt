#lang typed/racket/base

(provide ext-prove ext-plausible-pc? Timeout
         memo-ext-prove memo-ext-plausible #;miss/total ; debugging
         )

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

;; Stuff for memoizing `ext-prove`
(define-type Ext-Prove-Key (List -e (℘ -e) (Listof -γ) (HashTable -αₖ (℘ -ΓA))))
(define memo-ext-prove : (HashTable Ext-Prove-Key -R) (make-hash))

(: ->ext-prove-key : -M -Γ -e → Ext-Prove-Key)
(define (->ext-prove-key M Γ e)
  (define fvs (fv e))
  (match-define (-Γ φs _ γs) (Γ↓ Γ fvs))
  (define αₖs (for/set: : (℘ -αₖ) ([γ γs]) (-γ-callee γ)))
  (list e φs γs (span-M M αₖs)))

(: ext-prove : -M -Γ -e → -R)
(define (ext-prove M Γ e)
  #;(define t₀ (current-milliseconds))
  (with-debugging/off
    ((R)
     (hash-ref! memo-ext-prove
                (->ext-prove-key M Γ e)
                (λ ()
                  (define-values (base goal) (encode M Γ e))
                  (match/values (exec-check-sat base goal)
                    [('unsat _) '✓]
                    [(_ 'unsat) '✗]
                    [(_ _) '?]))))
    (define δt (- (current-milliseconds) t₀))
    (unless #f #;(< δt 300)
      (printf "ext-prove: ~a ⊢ ~a : ~a ~ams~n~n" (show-Γ Γ) (show-e e) R δt))))


;; Stuff for memoizing `ext-plausible-pc?`
(define-type Ext-Plausible-Key (List (℘ -e) (Listof -γ) (HashTable -αₖ (℘ -ΓA))))
(define memo-ext-plausible : (HashTable Ext-Plausible-Key Boolean) (make-hash))

(: ->ext-plausible-key : -M -Γ → Ext-Plausible-Key)
(define (->ext-plausible-key M Γ)
  (match-define (-Γ φs _ γs) Γ)
  (define αₖs (for/set: : (℘ -αₖ) ([γ γs]) (-γ-callee γ)))
  (list φs γs (span-M M αₖs)))

#|
(define total : Natural 0)
(define miss  : Natural 0)
(define (miss/total)
  (values miss total))
|#

(: ext-plausible-pc? : -M -Γ → Boolean)
(define (ext-plausible-pc? M Γ)
  ;(define t₀ (current-milliseconds))
  ;(set! total (+ 1 total))
  (with-debugging/off
    ((plaus?)
     (hash-ref! memo-ext-plausible
                (->ext-plausible-key M Γ)
                (λ ()
                  ;(set! miss (+ 1 miss))
                  (define-values (base _) (encode M Γ #|HACK|# -ff))
                  (case (exec-check-sat₀ base)
                    [(unsat) #f]
                    [(sat unknown) #t]))))
    (define δt (- (current-milliseconds) t₀))
    (unless (< δt (quotient (* (Timeout) 4) 5))
      (printf "ext-plausible? ~a : ~a ~ams~n~n" (show-Γ Γ) plaus? δt))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (set-default-options!)
  (set-options! #:timeout (Timeout)
                #:mbqi? #t
                #:macro-finder? #t
                #:rlimit 4000000))

(: exec-check-sat₀ : (→ Void) → Smt-Sat)
(define (exec-check-sat₀ asserts)
  (with-new-context
    (set-default-options!)
    (asserts)
    #;(check-sat/log 't0)
    (check-sat)))

(: exec-check-sat : (→ Void) (→ Z3-Ast) → (Values Sat-Result Sat-Result))
(define (exec-check-sat asserts goal)
  (match (with-new-context
           (set-default-options!)
           (asserts)
           (assert! (@/s 'is_false (goal)))
           (check-sat))
    ['false (values 'unsat 'unknown)]
    [a
     (values a
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
