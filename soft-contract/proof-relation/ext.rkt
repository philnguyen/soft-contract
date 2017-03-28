#lang typed/racket/base

(provide ext-prove)

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


(Sat-Result . ::= . Smt-Sat 'timeout)
(toggle-warning-messages! #f)

(: ext-prove : -M -Γ -t → -R)
(define (ext-prove M Γ t)
  (raw-ext-prove (span-M M (∪ (t->αₖs t) (Γ->αₖs Γ))) (-Γ-facts Γ) t))

(define/memo (raw-ext-prove [M : -M] [Γ : (℘ -t)] [t : -t]) : -R

  #;(begin
      (printf "M:~n")
      (for ([(a As) M])
        (printf "  * ~a ↦ ~a~n" (show-αₖ a) (set-map As show-ΓA)))
      (printf "Γ: ~a~n" (show-Γ Γ))
      (printf "-----------------------------------------~n")
      (printf "~a~n~n" (show-t t)))

  (define (set-default-options!)
    (set-options! #:timeout (assert (estimate-time-limit M Γ t) fixnum?)
                  #:mbqi? #t
                  #:macro-finder? #t
                  #:rlimit 4000000))

  (define-values (st-arities prims) (collect-usage M Γ t))
  (define-values (do-M fvs₁) (⦃M⦄ M))
  (define-values (do-Γ cnds do-t fvs₂)
    (let ([ctx₀ (Ctx ∅eq (make-hash))])
      (define-values (do-Γ      fvs₂) (⦃Γ⦄ ctx₀ Γ))
      (define-values (do-t cnds fvs₃) (⦃t⦄ ctx₀ t))
      (values do-Γ cnds do-t (∪ fvs₂ fvs₃))))
  (define-values (globals locals)
    (let ([fvs (∪ fvs₁ fvs₂)])
      (values (∩ fvs refs) (set-subtract fvs refs))))
  (define do-base
    (do set-default-options!
        (define-base-datatypes st-arities)
        (define-base-predicates prims)
        (declare-consts globals 'V)
        (iter-M do-M)
        (declare-consts locals 'V)
        (iter-M (set-map do-Γ assert-M))
        (iter-M (set-map cnds assert-M))))
  
  ;; TODO: Z3's incremental solver eats of memory and locks up my computer
  ;; if query has `is_int`, so I'm running 2 fresh queries worst case here.
  (with-debugging/off ((R) (case (run (do
                do-base
                (assert-false! (do-t))
                #;(λ ()
                  (print-current-assertions)
                  (printf "check false~n~n"))
                check-sat))
    [(unsat) '✓]
    [(sat unknown)
     (case (run (do
                  do-base
                  (assert-true! (do-t))
                  #;(λ ()
                    (print-current-assertions)
                    (printf "check true~n~n"))
                  check-sat))
       [(unsat) '✗]
       [(sat unknown) '?])]))
    (printf "  --> ~a~n~n" R)))

(: estimate-time-limit : -M (℘ -t) -t → Natural)
(define (estimate-time-limit M Γ t)
  (define Timeout-Factor 5)
  (define count
    (for/sum : Natural ([s (in-hash-values M)]) (set-count s)))
  (* count Timeout-Factor))
