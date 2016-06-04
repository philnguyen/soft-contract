#lang typed/racket/base

(provide ext-prove Γ-plausible?)

(require racket/match
         racket/port
         racket/system
         racket/string
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../runtime/main.rkt"
         "result.rkt"
         "translate.rkt")

(Sat-Result . ::= . 'Unsat 'Sat 'Unknown 'Timeout)

(: ext-prove : -M -Γ -e → -R)
(define (ext-prove M Γ e)
  (define-values (base goal) (encode M Γ e))
  (match/values (check-sat base goal)
    [('Unsat _) '✓]
    [(_ 'Unsat) '✗]
    [(_ _) '?]))

(: Γ-plausible? : -M -Γ → Boolean)
(define (Γ-plausible? M Γ)
  (define-values (base _) (encode M Γ -ff))
  (eq? 'Unsat (call `(,@base (check-sat)))))

(: check-sat : (Listof Sexp) Sexp → (Values Sat-Result Sat-Result))
(define (check-sat asserts goal)
  ;; TODO: can't do batch with push/pop. The incremental solver freezes my computer
  (match (call `(,@asserts (assert (is_false ,goal)) (check-sat)))
    ['Unsat (values 'Unsat 'Unknown)]
    [r₁ (values r₁ (call `(,@asserts (assert (is_truish ,goal)) (check-sat))))]))

(: call : (Listof Sexp) → Sat-Result)
(define (call stms)
  
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
  
  (define res
    (with-debugging
      ((ans)
       (with-output-to-string
         (λ () (system (format "echo \"~a\" | z3 -T:5 -memory:1000 -in -smt2" query)))))
      (printf "query:~n~a~nget: ~a~n~n" query ans)))
  (txt->result res))
