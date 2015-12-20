#lang typed/racket/base

(provide z3⊢ #|for debugging|# exp->sym)

(require
 racket/match racket/port racket/system racket/string racket/function racket/set
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
  (define-values (decls e->dec) (Γ->decls Γ))
  (cond
    [(exp->Z3 e->dec M σ Γ e) =>
     (λ ([concl : Sexp])
       (define decls*
         (match concl
           [(or `(is_int ,e*) `(not (is_int ,e*)) `(not (not (is_int ,e*)))) #:when e*
            (hack-decls-for-is-int decls (Z3-FV e*))]
           [_ decls]))
       (call-with decls* (Γ->premises e->dec M σ Γ) concl))]
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
;; I expose this publically just for debugging
(define exp->sym : (case-> [→ (HashTable -e Symbol)]
                           (-e → Symbol))
  (unique-name 'x_ #:subscript? #f))

(: Γ->decls : -Γ → (Values (Listof Sexp) (-e → (Option (Pairof Symbol Z3-Type)))))
;; Extract declarations from environment
(define (Γ->decls Γ)
  (define-set declared-exprs : -e)

  (define (more-precise-than? [T₁ : Z3-Type] [T₂ : Z3-Type])
    (match* (T₁ T₂)
      [('Int 'Real) #t]
      [(_ _) #f]))

  (define (upd-if-better [m : (HashTable Symbol Z3-Type)] [x : Symbol] [T : Z3-Type])
    (hash-update m x
                 (λ ([old-T : Z3-Type])
                   (if (T . more-precise-than? . old-T) T old-T))
                 (λ () T)))

  (define typeofs
    (for/fold ([typeofs : (HashTable Symbol Z3-Type) (hasheq)])
              ([φ (-Γ-facts Γ)])
      (match φ
        [(-@ (? Handled-Z3-pred? o) (list e) _)
         (define T (handled-Z3-pred->Z3-Type o))
         (declared-exprs-add! e)
         (define x (exp->sym e))
         (upd-if-better typeofs x T)]
        [(-@ (or '= 'equal?) (list e₁ e₂) _)
         (define (make-use-of-equal?! [b : Base] [e : -e])
           (define T
             (cond [(exact-integer? b) 'Int]
                   [(real? b) 'Real]
                   [else #f]))
           (cond
             [T
              (declared-exprs-add! e)
              (define x (exp->sym e))
              (upd-if-better typeofs x T)]
             [else typeofs]))
         (match* (e₁ e₂)
           [((? -b?) (? -b?)) typeofs]
           [((-b b₁) _) (make-use-of-equal?! b₁ e₂)]
           [(_ (-b b₂)) (make-use-of-equal?! b₂ e₁)]
           [(_ _) typeofs])]
        [_ typeofs])))
  
  (define decls
    (for/list : (Listof Sexp) ([(x T) (in-hash typeofs)])
      `(declare-const ,x ,T)))

  (values decls
          (λ (e)
            (and (∋ declared-exprs e)
                 (let ([x (exp->sym e)])
                   (cons x (hash-ref typeofs x)))))))

(: exp->Z3 : (-e → (Option (Pairof Symbol Z3-Type))) -M -σ -Γ -e → (Option Sexp)) ; not great for doc, #f ∈ Sexp
;; Translate restricted syntax into Z3 sexp
(define (exp->Z3 e->dec M σ Γ e)
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
      [(-@ 'integer? (list e) _)
       (cond
         [(go e) =>
          (λ ([z3-e : Sexp])
            (match (e->dec e)
              [(or #f (cons _ 'Real)) `(is_int ,z3-e)]
              [_ #f]))]
         [else #f])]
      [(-b b) (and (or (number? b) #;(string b)) b)]
      [_ (match (e->dec e)
           [(cons x _) x]
           [#f #f])])))

(: Γ->premises : (-e → (Option (Pairof Symbol Z3-Type))) -M -σ -Γ → (Listof Sexp))
;; Translate an environment into a list of Z3 premises
(define (Γ->premises e->dec M σ Γ)
  (for*/list : (Listof Sexp) ([e (-Γ-facts Γ)]
                              [s (in-value (exp->Z3 e->dec M σ Γ e))] #:when s)
    s))

;; translate Racket symbol to Z3 symbol
(: o->Z3 : Handled-Z3-op → Symbol)
(define (o->Z3 o)
  (case o
    [(equal?) '=]
    [else o]))

;; Z3's `is_int` doesn't work well if variables are declared as `Int` instead of `Real`
(define (hack-decls-for-is-int [decls : (Listof Sexp)] [xs : (Setof Symbol)]) : (Listof Sexp)
  (for/list ([decl decls])
    (match decl
      [`(declare-const ,x Int) #:when (∋ xs x)
       `(declare-const ,x Real)]
      [_ decl])))

;; Extract all free variables in Z3 clause
(define Z3-FV : (Sexp → (Setof Symbol))
  (match-lambda
    [`(,_ ,es ...) (for/union : (Setof Symbol) ([e es]) (Z3-FV (cast e Sexp)))]
    [(? symbol? x) {set x}]
    [_ ∅]))

;; Perform query/ies with given declarations, assertions, and conclusion,
;; trying to decide whether value definitely proves or refutes predicate
(: call-with : (Listof Sexp) (Listof Sexp) Sexp → -R)
(define (call-with decls prems concl)
  
  (define assert-prems : (Listof Sexp)
    (for/list ([prem prems]) `(assert ,prem)))
  
  (define (maybe-warn [res : String])
    (unless (regexp-match? #rx"^unknown" res)
      (printf "get unexpected result '~a' from Z3~n" res)))
  
  (match (call `(,@decls ,@assert-prems (assert ,concl) (check-sat)))
    [(regexp #rx"^unsat") 'X]
    [(regexp #rx"^sat")
     (match (call `(,@decls ,@assert-prems (assert (not ,concl)) (check-sat)))
       [(regexp #rx"^unsat") '✓]
       [(regexp #rx"^sat"  ) '?]
       [res (maybe-warn res) '?])]
    [res (maybe-warn res) '?]))

;; Perform system call to solver with given query
(: call : (Listof Sexp) → String)
(define (call cmds)
  (define query-str (string-join (map (curry format "~a") cmds) "\n"))
  (define ans
    (with-output-to-string
      (λ () (system (format "echo \"~a\" | z3 -in -smt2" query-str)))))
  ;(printf "query:~n~a~nget: ~a~n~n" query-str ans)
  ans)
