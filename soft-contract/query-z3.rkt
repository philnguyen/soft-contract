#lang typed/racket/base
(require racket/match racket/list racket/set racket/string racket/bool
         racket/port racket/system racket/function racket/pretty
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")

(provide z3⊢ Γ⊢₀)

(define-type Z3-Num (U 'Int 'Real))

;; Base proof relation
(define Γ⊢₀ : (Parameterof (-Γ -π → -R))
  (make-parameter
   (λ (Γ π)
     (log-warning "Base solver not set")
     '?)))

;; binary operators on reals
(define-type/pred -r² (U '+ '- '* '/ '> '< '>= '<= '= 'equal?))

;; Query external solver for provability relation
(: z3⊢ : -Γ -π → -R)
(define (z3⊢ Γ π)
  (define FVs (∪ (FV-Γ Γ) (FV-π π)))
  (define conclusion (t π))
  (define declarations
    (for/fold ([decs : (Listof Sexp) '()]) ([x FVs])
      (cond
        [(equal? '✓ ((Γ⊢₀) Γ (-π@ 'integer? (list (-x x)))))
         (cons `(declare-const ,x Int) decs)]
        [(equal? '✓ ((Γ⊢₀) Γ (-π@ 'real? (list (-x x)))))
         (cons `(declare-const ,x Real) decs)]
        [else decs])))
  (define premises
    (for*/list : (Listof Sexp) ([π Γ] [s (in-value (t π))] #:when s)
      `(assert ,s)))
  (call-with declarations premises conclusion))


(: t : -π → (Option Sexp))
;; Translate restricted syntax into Z3 sexp
(define (t π)
  (: go : -π → (Option Sexp))
  (define go
    (match-lambda
      [(-π@ (? -r²? r) (list π₁ π₂))
       (@? list (rkt→z3 r) (! (go π₁)) (! (go π₂)))]
      [(-π@ 'add1 (list π)) (@? list '+ (! (go π)) 1)]
      [(-π@ 'sub1 (list π)) (@? list '- (! (go π)) 1)]
      [(-π@ 'false? (list π)) (@? list 'not (! (go π)))]
      [(? -π@?) #f]
      [(-x x) x]
      [(-b b) b]))
  (go π))

(: γ : -Γ → (Listof Sexp))
;; Translate an environment into a list of expressions
(define (γ Γ)
  (for*/list : (Listof Sexp) ([π Γ] [s (in-value (t π))] #:when s) s))

;; translate Racket symbol to Z3 symbol
(: rkt→z3 : -r² → Symbol)
(define rkt→z3
  (match-lambda ['equal? '=] [r r]))

;; Perform query/ies with given declarations, assertions, and conclusion,
;; trying to decide whether value definitely proves or refutes predicate
(: call-with : (Listof Sexp) (Listof Sexp) Sexp → -R)
(define (call-with declarations premises conclusion)
  (printf "Query:~n~a~n"
          (pretty-format (append declarations premises (list conclusion)) 100))
  (match (call (pretty-format (append declarations premises (list conclusion)) 100))
    [(regexp #rx"^unsat") '✓]
    [(regexp #rx"^sat")
     (match (call (format "~a~n~a~n(assert ~a)~n(check-sat)~n" declarations premises conclusion))
       [(regexp #rx"^unsat") 'X]
       [_ #;(log-debug "?~n") '?])]
    [_ #;(log-debug "?~n")'?]))

;; Perform system call to solver with given query
(: call : String → String)
(define (call query)
  (log-debug "Called with:~n~a~n~n" query)
  (with-output-to-string
   (λ () (system (format "echo \"~a\" | z3 -in -smt2" query)))))
