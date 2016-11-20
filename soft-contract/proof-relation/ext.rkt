#lang typed/racket/base

(provide ext-prove ext-plausible-return? Timeout
         memo-ext-prove memo-ext-plausible #;miss/total ; debugging
         )

(require racket/match
         racket/set
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

(: ext-prove : -M -Γ -e → -R)
(define (ext-prove M Γ e)
  #;(define t₀ (current-milliseconds))
  (with-debugging/off
    ((R)
     (define fvs (fv e))
     (match-define (and Γ* (-Γ φs _ γs)) (Γ↓ Γ fvs))
     (define M* (span-M M (for/set: : (℘ -αₖ) ([γ γs]) (-γ-callee γ))))
     (hash-ref! memo-ext-prove
                (list e φs γs M*)
                (λ ()
                  (define-values (base goal) (encode M* Γ* e))
                  (match/values (exec-check-sat base goal)
                    [('unsat _) '✓]
                    [(_ 'unsat) '✗]
                    [(_ _) '?]))))
    (define δt (- (current-milliseconds) t₀))
    (unless #f #;(< δt 300)
      (printf "ext-prove: ~a ⊢ ~a : ~a ~ams~n~n" (show-Γ Γ) (show-e e) R δt))))


;; Stuff for memoizing `ext-plausible-pc?`
(define-type Ext-Plausible-Key (List -γ (℘ -e) (Listof -γ) (HashTable -αₖ (℘ -ΓA))))
(define memo-ext-plausible : (HashTable Ext-Plausible-Key Boolean) (make-hash))

#|
(define total : Natural 0)
(define miss  : Natural 0)
(define (miss/total)
  (values miss total))
|#

(: ext-plausible-return? : -M -Γ -γ -Γ → Boolean)
(define (ext-plausible-return? M Γₑᵣ γ Γₑₑ)
  (match-define (-γ αₖ _ sₕ sₓs) γ)
  (define fvsₑᵣ (apply ∪ (if (or (-λ? sₕ) (-case-λ? sₕ)) (fv sₕ) ∅eq)
                         (map fvₛ sₓs)))
  (match-define (and Γₑᵣ* (-Γ φs _ γs)) (Γ↓ Γₑᵣ fvsₑᵣ))
  (define M* (span-M M (set-add (for/set: : (℘ -αₖ) ([γ γs]) (-γ-callee γ)) αₖ)))
  (hash-ref! memo-ext-plausible
             (list γ φs γs M*)
             (λ ()
               (cond [(no-possible-conflict? Γₑᵣ γ Γₑₑ) #t]
                     [else (ext-plausible-pc? M* (-Γ-plus-γ Γₑᵣ* γ))]))))

(: ext-plausible-pc? : -M -Γ → Boolean)
(define (ext-plausible-pc? M Γ)
  (define-values (base _) (encode M Γ #|HACK|# -ff))
  (case (exec-check-sat₀ base)
    [(unsat) #f]
    [(sat unknown) #t]))

(: no-possible-conflict? : -Γ -γ -Γ → Boolean)
;; Heuristic check that there's no need for heavyweight SMT call
;; to filter out spurious return/blame
(define (no-possible-conflict? Γₑᵣ γ Γₑₑ)

  (: talks-about? : -Γ -e → Boolean)
  (define (talks-about? Γ e)
    (match-define (-Γ φs _ γs) Γ)
    (or (for/or : Boolean ([φ φs])
          (e-talks-about? φ e))
        (for/or : Boolean ([γ γs])
          (match-define (-γ _ _ sₕ sₓs) γ)
          (or (and sₕ (e-talks-about? sₕ e))
              (for/or : Boolean ([sₓ sₓs] #:when sₓ)
                (e-talks-about? sₓ e))))))

  (: e-talks-about? : -e -e → Boolean)
  (define (e-talks-about? e₁ e₂)
    (let loop ([e : -e e₁])
      (or (equal? e e₂)
          (match e
            [(-@ eₕ es _) (or (loop eₕ) (ormap loop es))]
            [_ #f]))))

  (match-define (-γ αₖ _ sₕ sₓs) γ)

  (match αₖ
    [(-ℬ (? list? xs) _ _)
     (not (or (for/or : Boolean ([x xs] [sₓ sₓs])
                (and sₓ
                     (Γₑᵣ . talks-about? . sₓ)
                     (Γₑₑ . talks-about? . (-x x))))
              (for/or : Boolean ([x (if sₕ (fv sₕ) ∅eq)])
                (and (Γₑᵣ . talks-about? . (-x x))
                     (Γₑₑ . talks-about? . (-x x))))))]
    ;; disable for monitoring blocks for now because can't know their shared free variables
    #;[(-ℳ x _ _ _ (-W¹ _ sₓ))
     (not (and sₓ
               (Γₑᵣ . talks-about? . sₓ)
               (Γₑₑ . talks-about? . (-x x))))]
    #;[(-ℱ x _ _ _ (-W¹ _ sₓ))
     (not (and sₓ
               (Γₑᵣ . talks-about? . sₓ)
               (Γₑₑ . talks-about? . (-x x))))]
    [_ #f]))


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
