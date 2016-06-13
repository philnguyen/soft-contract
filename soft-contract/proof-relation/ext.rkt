#lang typed/racket/base

(provide ext-prove Γ-plausible? Timeout)

(require racket/match
         racket/port
         racket/system
         racket/string
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "translate.rkt")

;; Max seconds per query
;; TODO: possible to have something deterministic instead?
(define-parameter Timeout : Natural 2)

(Sat-Result . ::= . 'Unsat 'Sat 'Unknown 'Timeout)

(: ext-prove : -M -Γ -e → -R)
(define (ext-prove M Γ e)
  (define t₀ (current-milliseconds))
  (with-debugging/off
    ((ans)
     (define-values (base goal) (encode M Γ e))
     (match/values (check-sat base goal)
       [('Unsat _) '✓]
       [(_ 'Unsat) '✗]
       [(_ _) '?]))
    #;(begin ; manual profiling
      (define δt (- (current-milliseconds) t₀))
      (accum-data! (list Γ e ans) δt))
    #;(begin
      (match-define (-Γ φs _ γs) Γ)
      (define-values (base goal) (encode M Γ e))
      (for ([φ φs]) (printf "~a~n" (show-φ φ)))
      (for ([γ γs])
        (match-define (-γ _ bnd blm?) γ)
        (printf "~a  blm? : ~a~n" (show-binding bnd) blm?))
      (printf "-----------------------------------------~a~n" ans)
      (printf "~a~n~n" (show-e e))
      (printf "Translation:~n")
      (for ([stm base]) (printf "~a~n" stm))
      (printf "=========================================~n")
      (printf "~a~n~n" goal))
    ))

(: Γ-plausible? : -M -Γ → Boolean)
(define (Γ-plausible? M Γ)
  (define-values (base _) (encode M Γ -ff))
  (not
   (eq? 'Unsat (call `(,@base
                       ";; Check if path-condition is plausible"
                       (check-sat))))))

(: check-sat : (Listof Sexp) Sexp → (Values Sat-Result Sat-Result))
(define (check-sat asserts goal)
  ;; TODO: can't do batch with push/pop. The incremental solver freezes my computer
  (match (call `(,@asserts
                 ";; Unsat means M Γ ⊢ e : ✓"
                 (assert (is_false ,goal))
                 (check-sat)))
    ['Unsat (values 'Unsat 'Unknown)]
    [r₁ (values r₁ (call `(,@asserts
                           ";; Unsat means M Γ ⊢ e : ✗"
                           (assert (is_truish ,goal))
                           (check-sat))))]))

;(: call : (Listof Sexp) → Sat-Result)
(define/memo (call [stms : (Listof Sexp)]) : Sat-Result
  
  (: txt->result : String → Sat-Result)
  (define/match (txt->result s)
    [((regexp #rx"^unsat")) 'Unsat]
    [((regexp #rx"^sat(.*)")) 'Sat]
    [((regexp #rx"^unknown")) 'Unknown]
    [((regexp #rx"^timeout")) 'Timeout]
    [(str) (error 'check-sat "unexpected output from solver: ~a~nquery:~n~a~n" str query)])

  (define query
    (string-join (for/list : (Listof String) ([stm stms]) (format "~a" stm))
                 "\n"))

  ;(define t₀ (current-milliseconds))
  (define res
    (with-debugging/off
      ((ans)
       (with-output-to-string
         (λ ()
           (system (format "echo \"~a\" | z3 -T:~a -memory:1000 -in -smt2" query (Timeout))))))
      #;(match ans
          [_ ;(regexp #rx"^timeout")
           (printf "query:~n~a~nget: ~a~n~n" query ans)]
          [_ (void)])
      (begin
        (define δt (- (current-milliseconds) t₀))
        (accum-data! query δt))))
  (txt->result res))
