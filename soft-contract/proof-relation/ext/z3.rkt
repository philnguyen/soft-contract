#lang typed/racket/base

(provide z3⊢ #|for debugging|# exp->sym)

(require
 racket/match racket/port racket/system racket/string racket/function
 "../../utils/def.rkt" "../../utils/set.rkt" "../../utils/eval.rkt" "../../utils/debug.rkt"
 "../../utils/pretty.rkt" "../../utils/untyped-macros.rkt"
 "../../ast/definition.rkt" "../../ast/meta-functions.rkt"
 "../../primitives/utils.rkt"
 "../../runtime/path-inv.rkt" "../../runtime/simp.rkt" "../../runtime/store.rkt"
 "../../runtime/summ.rkt"
 "../utils.rkt"
 "../result.rkt")

;; Query external solver for provability relation
(: z3⊢ : -M -σ -Γ -e → -R)
(define (z3⊢ M σ Γ e)
  ;(printf "~a~n⊢~n~a~n~n" (show-Γ Γ) (show-e e))
  (define-values (decls declared-exps) (Γ->decls Γ))
  (cond
    [(exp->Z3 M σ Γ declared-exps e) =>
     (λ ([concl : Sexp])
       (call-with decls (Γ->premises declared-exps M σ Γ) concl))]
    [else '?]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Z3-Type (U 'Int 'Real))

;; binary operators on reals
(define-type/pred Handled-Z3-pred
  (U 'integer? 'exact-integer? 'exact-positive-integer? 'exact-nonnegative-integer?
     'inexact-real? 'rational? 'fixnum? 'flonum? 'single-flonum? 'double-flonum? 'real?))
(define-type/pred Handled-Z3-op (U '+ '- '* '/ '> '< '>= '<= '= 'equal?))

(define (handled-Z3-pred->Z3-Type [t : Handled-Z3-pred]) : Z3-Type
  (cond
    [(∋ (hash-ref implications t →∅) 'integer?) 'Int]
    [(∋ (hash-ref implications t →∅) 'real?) 'Real]
    [else (error 'handled-Z3-pred->Z3-Type "unexpected ~a" t)]))

;; Convert each expression to a fresh memoized symbol
(define exp->sym : (case-> [→ (HashTable -e Symbol)]
                           (-e → Symbol))
  (unique-name 'x_ #:subscript? #f))

(: Γ->decls : -Γ → (Values (Listof Sexp) (Setof -e)))
;; Extract declarations from environment
(define (Γ->decls Γ)
  (define-set declared-exprs : -e)

  (define (more-precise-than? [T₁ : Z3-Type] [T₂ : Z3-Type])
    (match* (T₁ T₂)
      [('Int 'Real) #t]
      [(_ _) #f]))

  (define typeofs
    (for/fold ([typeofs : (HashTable Symbol Z3-Type) (hasheq)])
              ([φ (-Γ-facts Γ)])
      (match φ
        [(-@ (? Handled-Z3-pred? o) (list e) _)
         (declared-exprs-add! e)
         (define T (handled-Z3-pred->Z3-Type o))
         (define x (exp->sym e))
         (hash-update typeofs x
                      (λ ([old : Z3-Type])
                        (if (T . more-precise-than? . old) T old))
                      (λ () T))]
        [_ typeofs])))
  
  (define decls
    (for/list : (Listof Sexp) ([(x T) (in-hash typeofs)])
      `(declare-const ,x ,T)))

  (values decls declared-exprs))

(: exp->Z3 : -M -σ -Γ (Setof -e) -e → (Option Sexp)) ; not great for doc, #f ∈ Sexp
;; Translate restricted syntax into Z3 sexp
(define (exp->Z3 M σ Γ declared e)
  (define-values (e* _) (⇓₁ M σ Γ e))
  #;(when (match? e (-@ '= _ _))
    (printf "~a ⊢ ~a ⇓₁ ~a~n" (show-Γ Γ) (show-e e) (show-e e*)))
  (let go : (Option Sexp) ([e : -e e*])
    (match e
      [(-@ (? Handled-Z3-op? o) (list e₁ e₂) _)
       (@? list (o->Z3 o) (! (go e₁)) (! (go e₂)))]
      [(-@ 'add1 (list e) _) (@? list '+ (! (go e)) 1)]
      [(-@ 'sub1 (list e) _) (@? list '- (! (go e)) 1)]
      [(-@ 'not (list e) _) (@? list 'not (! (go e)))]
      [(-@ 'zero? (list e) _) (@? list '= (! (go e)) 0)]
      [(-@ 'negative? (list e) _) (@? list '< (! (go e)) 0)]
      [(-@ (or 'positive? 'exact-positive-integer?) (list e) _) (@? list '> (! (go e)) 0)]
      [(-@ 'exact-nonnegative-integer? (list e) _) (@? list '>= (! (go e)) 0)]
      [(-@ 'even? (list e) _) (@? list '= (@? list 'mod (! (go e)) 2) 0)]
      [(-@ 'odd? (list e) _) (@? list '= (@? list 'mod (! (go e)) 2) 1)]
      [(-b b) (and (or (number? b) #;(string b)) b)]
      [_ (and (∋ declared e) (exp->sym e))])))

(: Γ->premises : (Setof -e) -M -σ -Γ → (Listof Sexp))
;; Translate an environment into a list of Z3 premises
(define (Γ->premises declared M σ Γ)
  (for*/list : (Listof Sexp) ([e (-Γ-facts Γ)]
                              [s (in-value (exp->Z3 M σ Γ declared e))] #:when s)
    s))

;; translate Racket symbol to Z3 symbol
(: o->Z3 : Handled-Z3-op → Symbol)
(define (o->Z3 o)
  (case o
    [(equal?) '=]
    [else o]))

;; Perform query/ies with given declarations, assertions, and conclusion,
;; trying to decide whether value definitely proves or refutes predicate
(: call-with : (Listof Sexp) (Listof Sexp) Sexp → -R)
(define (call-with decls prems concl)
  (define assert-prems
    (for/list : (Listof Sexp) ([prem prems]) `(assert ,prem)))
  (match (call `(,@decls ,@assert-prems (assert ,concl) (check-sat)))
    [(regexp #rx"^unsat") 'X]
    [(regexp #rx"^sat")
     (match (call `(,@decls ,@assert-prems (assert (not ,concl)) (check-sat)))
       [(regexp #rx"^unsat") '✓]
       [(regexp #rx"^sat"  ) '?]
       [res (printf "get unexpected result '~a' from Z3~n" res) '?])]
    [res (printf "get unexpected result '~a' from Z3~n" res) '?]))

;; Perform system call to solver with given query
(: call : (Listof Sexp) → String)
(define (call cmds)
  (define query-str (string-join (map (curry format "~a") cmds) "\n"))
  ;(printf "query:~n~a~n~n" query-str)
  (with-output-to-string
   (λ () (system (format "echo \"~a\" | z3 -in -smt2" query-str)))))
