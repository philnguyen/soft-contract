#lang typed/racket/base

(provide z3⊢ get-model #|for debugging|# exp->sym sym->exp)

(require racket/match
         racket/port
         racket/system
         racket/string
         (except-in racket/function arity-includes?)
         racket/set
         "../../utils/main.rkt"
         "../../ast/main.rkt"
         "../../primitives/utils.rkt"
         "../../runtime/main.rkt"
         "../result.rkt")

;; Query external solver for provability relation
(: z3⊢ : (℘ -e) -e → -R)
(define (z3⊢ φs e)
  (match (es⊢e->Z3 φs e)
    [(list decls prems concl)
     (with-debugging/off
       ((ans) (call-with decls prems concl))
       (printf "Z3: ~a ⊢ ~a : ~a~n" (set-map φs show-e) (show-e e) ans))]
    [#f '?]))

(: get-model : (℘ -e) → (Option (HashTable -e Base)))
;; Generate a model for given path invariant
(define (get-model φs)
  (define-values (decls props) (es->Z3 φs))
  (match (check-sat decls props #:produce-model? #t)
    ['Unsat (error 'get-model "unsat")]
    ['Unknown (error 'get-model "unknown")]
    [`(Sat ,m) #:when m
     (for/hash : (HashTable -e Base) ([(x v) m])
       (values (sym->exp x) v))]
    [`(Sat #f) #f]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: es⊢e->Z3 : (℘ -e) -e →  (Option (List (Listof Sexp) (Listof Sexp) Sexp)))
;; Translate path condition and goal into Z3 declarations and formula
(define (es⊢e->Z3 φs e)
  (define-values (decls₀ e->dec) (es->decls φs))
  #;(begin
    (printf "es⊢e->Z3:~n")
    (printf "  - ~a ⊢ ~a~n" (set-map φs show-e) (show-e e))
    (printf "  -> decls₀: ~a~n" decls₀)
    (printf "~n"))
  (cond
    [(exp->Z3 e->dec φs e) =>
     (λ ([concl : Sexp])
       (define xs-adjusted (FV-for-is_int concl))
       (define-values (decls is_int-premises) (hack-decls-for-is_int decls₀ xs-adjusted))
       (define premises (append is_int-premises (es->premises e->dec φs)))
       (list decls premises concl))]
    [else #f]))

(: es->Z3 : (℘ -e) → (Values (Listof Sexp) (Listof Sexp)))
;; Translate path condition into Z3 declarations and formula
(define (es->Z3 φs)
  (define-values (decls₀ e->dec) (es->decls φs))
  (define props (es->premises e->dec φs))
  (define adjusted-vars-for-is_int
    (for/fold ([xs : (℘ Symbol) ∅]) ([prop props])
      (∪ xs (FV-for-is_int prop))))
  (define-values (decls is_int-premises) (hack-decls-for-is_int decls₀ adjusted-vars-for-is_int))
  (values decls (append is_int-premises props)))

(: hack-decls-for-is_int : (Listof Sexp) (℘ Symbol) → (Values (Listof Sexp) (Listof Sexp)))
;; Z3's `is_int` doesn't work well if variables are declared as `Int` instead of `Real`
(define (hack-decls-for-is_int decls xs)
  (values
   (for/list ([decl decls])
     (match decl
       [`(declare-const ,x Int) #:when (∋ xs x)
        `(declare-const ,x Real)]
       [_ decl]))
   (for/list ([x xs]) `(is_int ,x))))

(: FV-for-is_int : Sexp → (℘ Symbol))
;; Check if formula is of form `(... (is_int e))`. Return all FV in `e` if so.
(define (FV-for-is_int e)
  (match e
    [(or `(is_int ,e*) `(not (is_int ,e*)) `(not (not (is_int ,e*)))) #:when e*
     (Z3-FV e*)]
    [_ ∅]))

(Z3-Type . ::= . 'Int 'Real)

;; binary operators on reals
(Handled-Z3-pred . ::= . 'integer? 'exact-integer? 'exact-positive-integer? 'exact-nonnegative-integer?
                         'inexact-real? 'rational? 'fixnum? 'flonum? 'single-flonum? 'double-flonum? 'real?)
(Handled-Z3-op . ::= . '+ '- '* '/ '> '< '>= '<= '= 'equal?)

(define (handled-Z3-pred->Z3-Type [t : Handled-Z3-pred]) : Z3-Type
  (cond
    [(∋ (hash-ref implications t →∅) 'integer?) 'Int]
    [(∋ (hash-ref implications t →∅) 'real?) 'Real]
    [else (error 'handled-Z3-pred->Z3-Type "unexpected ~a" t)]))

;; Convert each expression to a fresh memoized symbol
;; I expose this publically just for debugging
(define-values (exp->sym sym->exp _) ((inst unique-sym -e) 'x_ #:transform-index values))

(: es->decls : (℘ -e) → (Values (Listof Sexp) (-e → (Option (Pairof Symbol Z3-Type)))))
;; Extract declarations from environment
(define (es->decls φs)
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
              ([φ φs])
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

(: exp->Z3 : (-e → (Option (Pairof Symbol Z3-Type))) (℘ -e) -e → (Option Sexp)) ; not great for doc, #f ∈ Sexp
;; Translate restricted syntax into Z3 sexp
(define (exp->Z3 e->dec φs e)
  (with-debugging/off
    ((ans)
     (let go : (Option Sexp) ([e : -e e])
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
    (printf "exp->Z3: ~a ↦ ~a~n" (show-e e) ans)))

(: es->premises : (-e → (Option (Pairof Symbol Z3-Type))) (℘ -e) → (Listof Sexp))
;; Translate an environment into a list of Z3 premises
(define (es->premises e->dec φs)
  (for*/list : (Listof Sexp) ([e φs]
                              [s (in-value (exp->Z3 e->dec φs e))] #:when s)
    s))

;; translate Racket symbol to Z3 symbol
(: o->Z3 : Handled-Z3-op → Symbol)
(define (o->Z3 o)
  (case o
    [(equal?) '=]
    [else o]))

;; Extract all free variables in Z3 clause
(define Z3-FV : (Sexp → (℘ Symbol))
  (match-lambda
    [`(,_ ,es ...) (for/union : (℘ Symbol) ([e es]) (Z3-FV (cast e Sexp)))]
    [(? symbol? x) {set x}]
    [_ ∅]))

(define-type Sat-Result (U 'Unsat
                           (List 'Sat (Option (HashTable Symbol Real)))
                           'Unknown))

;; Perform query/ies with given declarations, assertions, and conclusion,
;; trying to decide whether value definitely proves or refutes predicate
(: call-with : (Listof Sexp) (Listof Sexp) Sexp → -R)
(define (call-with decls prems concl)
  (case (check-sat decls (cons concl prems))
    [(Unsat) '✗]
    [(Unknown) '?]
    [else
     (case (check-sat decls (cons `(not ,concl) prems))
       [(Unsat) '✓]
       [else '?])]))

(: check-sat ([(Listof Sexp) (Listof Sexp)] [#:produce-model? Boolean] . ->* . Sat-Result))
;; Check if given model is possible
(define (check-sat decls props #:produce-model? [produce-model? #f])

  (define assertions : (Listof Sexp)
    (for/list ([prop props]) `(assert ,prop)))

  (txt->sat-result
   (call `(,@decls ,@assertions (check-sat) ,@(if produce-model? '((get-model)) '())))))

;; Perform system call to solver with given query
(: call : (Listof Sexp) → String)
(define (call cmds)
  (define query-str (string-join (map (curry format "~a") cmds) "\n"))
  (with-debugging/off
    ((ans)
     (with-output-to-string
       (λ () (system (format "echo \"~a\" | z3 -T:5 -in -smt2" query-str)))))
    (printf "query:~n~a~nget: ~a~n~n" query-str ans)))

(: txt->sat-result : String → Sat-Result)
(define (txt->sat-result str)
  (match str
    [(regexp #rx"^unsat") 'Unsat]
    [(regexp #rx"^sat(.*)" (list _ (? string? mdl-str)))
     (with-input-from-string mdl-str
       (λ ()
         (match (parameterize ([read-decimal-as-inexact #f])
                  (read))
           [(list 'model lines ...)
            #;(begin
                (printf "Model:~n")
                (for ([l lines]) (printf "~a~n" l)))
            (define m
              (for/hash : (HashTable Symbol Real) ([line : Any (in-list lines)])
                (match-define `(define-fun ,(? symbol? a) () ,_ ,e) line)
                #;(printf "e: ~a~n" e)
                (define res
                  (let go : Real ([e : Any e])
                       (match e
                         [`(+ ,eᵢ ...) (apply + (map go eᵢ))]
                         [`(- ,e₁ ,eᵢ ...) (apply - (go e₁) (map go eᵢ))]
                         [`(* ,eᵢ ...) (apply * (map go eᵢ))]
                         [`(/ ,e₁ ,eᵢ ...) (apply / (go e₁) (map go eᵢ))]
                         [`(,(or '^ '** 'expt) ,e₁ ,e₂) (assert (expt (go e₁) (go e₂)) real?)]
                         [(? real? x) x])))
                (values a res)))
            `(Sat ,m)]
           [_ `(Sat #f)])))]
    [res
     (unless (regexp-match? #rx"^unknown" res)
       (printf "get unexpected result '~a' from Z3~n" res))
     'Unknown]))
