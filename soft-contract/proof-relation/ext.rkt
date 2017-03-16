#lang typed/racket/base

(provide ext-prove #;ext-plausible-return? Timeout
         ;memo-ext-prove memo-ext-plausible #;miss/total ; debugging
         )

(require racket/match
         racket/set
         racket/list
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
#;(define-type Ext-Prove-Key (List -e (℘ -e) (Listof -γ) (HashTable -αₖ (℘ -ΓA))))
#;(define memo-ext-prove : (HashTable Ext-Prove-Key -R) (make-hash))

(: ext-prove : -M -Γ -e → -R)
(define (ext-prove M Γ e)
  #;(begin
    (printf "ext-prove~n")
    (printf "M~n")
    (for ([(a As) (in-hash M)])
      (printf "  - ~a ↦ (~a)~n" (show-αₖ a) (set-count As))
      (for ([A (in-set As)])
        (printf "    * ~a~n" (show-ΓA A))))
    (printf "Γ:~n")
    (for ([e (-Γ-facts Γ)])
      (printf "  - ~a~n" (show-e e)))
    (for ([γ (-Γ-tails Γ)])
      (printf "  - ~a~n" (show-γ γ)))
    (printf "-----------------------------------------~n")
    (printf "   ~a~n" (show-e e)))

  #;(define t₀ (current-milliseconds))
  '?
  #;(with-debugging/off
    ((R)
     (define fvs (with-measuring/off 'ext-prove:fv (fv e)))
     (match-define (and Γ* (-Γ φs _ γs)) (with-measuring/off 'ext-prove:Γ↓ (Γ↓ Γ fvs)))
     (define M* (with-measuring/off 'ext-prove:span-M (span-M M (for/set: : (℘ -αₖ) ([γ γs]) (-γ-callee γ)))))
     (hash-ref! memo-ext-prove
                (list e φs γs M*)
                (λ ()
                  #;(begin
                    (printf "Simplified M~n")
                    (for ([(a As) (in-hash M*)])
                      (printf "  - ~a ↦ (~a)~n" (show-αₖ a) (set-count As))
                      (for ([A (in-set As)])
                        (printf "    * ~a~n" (show-ΓA A))))
                    (printf "Simplified Γ:~n")
                    (for ([e (-Γ-facts Γ*)])
                      (printf "  - ~a~n" (show-e e)))
                    (for ([γ (-Γ-tails Γ*)])
                      (printf "  - ~a~n~n" (show-γ γ))))
                  (define-values (base goal) (with-measuring/off 'ext-prove:encode (encode M* Γ* e)))
                  
                  #;(define t₀ (current-milliseconds))
                  (define ans : -R
                    (match/values (exec-check-sat base goal)
                      [('unsat _) '✓]
                      [(_ 'unsat) '✗]
                      [(_ _) '?]))
                  #;(define δt (- (current-milliseconds) t₀))

                  #;(when (> δt (quotient (* (Timeout) 2) 3))
                    (printf "exec-check-sat:~n")
                    (printf "M:~n")
                    (for ([(αₖ ΓAs) (in-hash M*)])
                      (printf "  - ~a ↦ ~a~n" (show-αₖ αₖ) (set-count ΓAs))
                      (for ([ΓA (in-set ΓAs)])
                        (printf "    + ~a~n" (show-ΓA ΓA))))
                    (printf "Γ:~n")
                    (match-let ([(-Γ φs _ γs) Γ*])
                      (for ([φ (in-set φs)])
                        (printf "  - ~a~n" (show-e φ)))
                      (for ([γ (in-list γs)])
                        (printf "  - ~a~n" (show-γ γ))))
                    (printf "-----------------------------------------~a, ~a~n" ans δt)
                    (printf "~a~n~n" (show-e e)))

                  ans)))
    (define δt (- (current-milliseconds) t₀))
    (unless #f #;(< δt 300)
      (printf "ext-prove: ~a ⊢ ~a : ~a ~ams~n~n" (show-Γ Γ) (show-e e) R δt))))


;; Stuff for memoizing `ext-plausible-pc?`
#;(define-type Ext-Plausible-Key (List -γ (℘ -e) (Listof -γ) (HashTable -αₖ (℘ -ΓA))))
#;(define memo-ext-plausible : (HashTable Ext-Plausible-Key Boolean) (make-hash))

#|
(define total : Natural 0)
(define miss  : Natural 0)
(define (miss/total)
  (values miss total))
|#

#;(: ext-plausible-return? : -M -Γ -γ -Γ → Boolean)
#;(define (ext-plausible-return? M Γₑᵣ γ Γₑₑ)
  (match-define (-γ αₖ _ sₕ sₓs) γ)
  (define fvsₑᵣ (with-measuring/off 'ext-plaus:fv (apply ∪ (if (or (-λ? sₕ) (-case-λ? sₕ)) (fv sₕ) ∅eq)
                         (map fvₛ sₓs))))
  (match-define (and Γₑᵣ* (-Γ φs _ γs)) (with-measuring/off 'ext-plaus:Γ↓ (Γ↓ Γₑᵣ fvsₑᵣ)))
  (define M* (with-measuring/off 'ext-plaus:span-M (span-M M (set-add (for/set: : (℘ -αₖ) ([γ γs]) (-γ-callee γ)) αₖ))))
  (hash-ref! memo-ext-plausible
             (list γ φs γs M*)
             (λ ()
               (with-debugging/off
                 ((ans₁)
                  (cond [(with-measuring/off 'ext-plaus:mb-no-cnflct? (maybe-no-conflict? Γₑᵣ γ Γₑₑ)) #t]
                        [else
                         #;(begin
                           (printf "ext-plausible?~n")
                           (printf "M~n")
                           (for ([(a As) (in-hash M*)])
                             (printf "  - ~a ↦ (~a)~n" (show-αₖ a) (set-count As))
                             (for ([A (in-set As)])
                               (printf "    * ~a~n" (show-ΓA A))))
                           (printf "Γ:~n")
                           (for ([e (-Γ-facts Γₑᵣ*)])
                             (printf "  - ~a~n" (show-e e)))
                           (for ([γ (-Γ-tails Γₑᵣ*)])
                             (printf "  - ~a~n" (show-γ γ)))
                           (printf "-----------------------------------------~n")
                           (printf "   ~a~n" (show-γ γ)))
                         (ext-plausible-pc? M* (-Γ-plus-γ Γₑᵣ* γ))]))
                 (define ans₂ (ext-plausible-pc? M (-Γ-plus-γ Γₑᵣ γ)))
                 (unless (equal? ans₁ ans₂)
                   (printf "inconsistency in optimized `ext-plausible-return?`~n")
                   (printf "unoptimized:~n")
                   (printf "- M: ~a~n" (show-M M))
                   (printf "- Γₑᵣ: ~a~n" (show-Γ (-Γ-plus-γ Γₑᵣ γ)))
                   (printf "- ans: ~a~n" ans₂)
                   (printf "optimized:~n")
                   (printf "- M*: ~a~n" (show-M M*))
                   (printf "- Γₑᵣ*: ~a~n" (show-Γ (-Γ-plus-γ Γₑᵣ* γ)))
                   (printf "- ans: ~a~n" ans₁)
                   (error 'inconsistency))))))

#;(: ext-plausible-pc? : -M -Γ → Boolean)
#;(define (ext-plausible-pc? M Γ)
  (define-values (base _) (with-measuring/off 'ext-plaus:encode (encode M Γ #|HACK|# -ff)))
  
  #;(define t₀ (current-milliseconds))
  (define ans : Boolean
    (case (exec-check-sat₀ base)
      [(unsat) #f]
      [(sat unknown) #t]))
  #;(define δt (- (current-milliseconds) t₀))
  #;(when (> δt (quotient (* (Timeout) 2) 3))
    (printf "exec-check-sat₀:~n")
    (printf "M:~n")
    (for ([(αₖ ΓAs) (in-hash M)])
      (printf "  - ~a ↦ ~a~n" (show-αₖ αₖ) (set-count ΓAs))
      (for ([ΓA (in-set ΓAs)])
        (printf "    + ~a~n" (show-ΓA ΓA))))
    (printf "Γ:~n")
    (match-let ([(-Γ φs _ γs) Γ])
      (for ([φ (in-set φs)])
        (printf "  - ~a~n" (show-e φ)))
      (for ([γ (in-list γs)])
        (printf "  - ~a~n" (show-γ γ))))
    (printf "-----------------------------------------~a, ~a~n~n" ans δt))

  ans)

#;(: maybe-no-conflict? : -Γ -γ -Γ → Boolean)
;; Heuristic check that there's no need for heavyweight SMT call
;; to filter out spurious return/blame
#;(define (maybe-no-conflict? Γₑᵣ γ Γₑₑ)

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
    [(-ℬ (? list? xs) _ _ #;_)
     (not (or (for/or : Boolean ([x xs] [sₓ sₓs])
                (and sₓ
                     (Γₑᵣ . talks-about? . sₓ)
                     (Γₑₑ . talks-about? . (-x x))))
              (for/or : Boolean ([x (if sₕ (fv sₕ) ∅eq)])
                (and (Γₑᵣ . talks-about? . (-x x))
                     (Γₑₑ . talks-about? . (-x x))))))]
    [(-ℳ x _ _ _ _)
     (match-define (list sₓ) sₓs)
     (not (and sₓ
               (Γₑᵣ . talks-about? . sₓ)
               (Γₑₑ . talks-about? . (-x x))))]
    [(-ℱ x _ _ _ _)
     (match-define (list sₓ) sₓs)
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
    (with-measuring/off 'exec-check-sat₀:set-options (set-default-options!))
    (with-measuring/off 'exec-check-sat₀:asserts (asserts))
    #;(check-sat/log 't0)
    (with-measuring/off 'exec-check-sat₀:check-sat (check-sat))))

(: exec-check-sat : (→ Void) (→ Z3-Ast) → (Values Sat-Result Sat-Result))
(define (exec-check-sat asserts goal)
  (match (with-new-context
           (with-measuring/off 'exec-check-sat:set-options (set-default-options!))
           (with-measuring/off 'exec-check-sat:asserts (asserts))
           (with-measuring/off 'exec-check-sat:assert₁ (assert! (@/s 'is_false (goal))))
           (with-measuring/off 'exec-check-sat:check-sat (check-sat)))
    ['false (values 'unsat 'unknown)]
    [a
     (values a
             (with-new-context
               (with-measuring/off 'exec-check-sat:set-options (set-default-options!))
               (with-measuring/off 'exec-check-sat:asserts (asserts))
               (with-measuring/off 'exec-check-sat:assert₁ (assert! (@/s 'is_truish (goal))))
               (with-measuring/off 'exec-check-sat:check-sat (check-sat))))])
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
