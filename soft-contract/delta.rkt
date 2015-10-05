#lang typed/racket/base
(require
 racket/match racket/set racket/bool racket/math racket/contract
 "utils.rkt" "ast.rkt" "runtime.rkt" "provability.rkt"
 (for-syntax racket/base syntax/parse racket/contract racket/pretty racket/match
             racket/bool racket/list racket/function "prims.rkt")
 ;"make-delta.rkt"
 )
(provide (all-defined-out))

;; Language definition for `δ` begins here
(begin-for-syntax

  (define-syntax-class ctc
    #:description "primitive contract"
    (pattern (~or x:id ((~literal and/c) sub:id ...))))
  
  (define-syntax-class sig
    #:description "primitive signature"
    (pattern (d:ctc (~literal ->) r:ctc)))

  (define/contract (generate-δ-clause M σ Γ o Ws loc row)
    (syntax? syntax? syntax? syntax? syntax? syntax? syntax? . -> . (listof syntax?))
    (syntax-parse row
      [(#:predicate p:id)
       (generate-δ-clause M σ Γ o Ws loc #`(#:predicate p (any/c)))]
      [(#:predicate p:id (dom:ctc ...))
       (list #`(error "TODO" (quote #,(syntax->datum #'p))))]
      [(#:batch (ops:id ...) main:sig refinements:sig ...)
       (apply
        append
        (for/list ([op (syntax->list #'(ops ...))])
          (generate-δ-clause
           M σ Γ o Ws loc
           #`(#,op main refinements ... #:errors-when))))]
      #;[(op:id main:sig refinements:sig ...)
       (generate-δ-clause
        M σ Γ o Ws loc
        #`(op:id main:sig refinements:sig #:errors-when))]
      #;[(op:id main:sig refinements:sig ... #:errors-when (d:ctc ...))
       (list #`(error "TODO" (quote #,(syntax->datum #'op))))]))
  
  (define/contract (generate-δ-clauses M σ Γ o Ws loc)
    (syntax? syntax? syntax? syntax? syntax? syntax? . -> . (listof syntax?))
    (append-map (curry generate-δ-clause M σ Γ o Ws loc)
                (syntax->list prims))))


(define-syntax (generate-δ-body stx)
  (syntax-parse stx
    [(_ M:id σ:id Γ:id o:id Ws:id loc:id)
     (define clauses (generate-δ-clauses #'M #'σ #'Γ #'o #'Ws #'loc))
     #`(match o #,@clauses)]))

(: δ : -M -σ -Γ -o (Listof -WV) -src-loc → -AΓs)
(define (δ M σ Γ o Ws loc)
  (generate-δ-body M σ Γ o Ws loc))

#|
(: δ : -M -σ -Γ -o (Listof -WV) -src-loc → -AΓs)
;; Interpret primitive operations.
;; Return (Widened_Store × P((Result|Error)×Updated_Facts))
(define (δ M σ Γ o Ws loc)
  (match-define (-src-loc l pos) loc)
  
  (: ans-bad : Mon-Party Mon-Party -V -V → (-Γ → -AΓ))
  (define ((ans-bad l+ lo P V) Γ)
    (-AΓ (-blm l+ lo P (list V)) Γ))
  
  (define-syntax-rule (with-guarded-arity n e ...)
    (cond
      [(= n (length Ws)) e ...]
      [else
       (-AΓ (-blm l (show-o o)
                  (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤)
                  (WVs->Vs Ws))
            Γ)]))
  
  
  (match o
    ;; Primitive predicate
    [(? -pred₁?)
     (with-guarded-arity 1
       (define V_a
         (match (apply MσΓ⊢oW M σ Γ o Ws)
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (-AΓ (list V_a) Γ))]

    [(? -pred₂?)
     (with-guarded-arity 2
       (define V_a
         (match (apply MσΓ⊢oW M σ Γ o Ws)
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (-AΓ (list V_a) Γ))]

    ;; Multiple values
    ['values (-AΓ (map (inst -W-x -V) Ws) Γ)]
    
    ['vector-length
     (with-guarded-arity 1
       (match-define (list (and W (-W V _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ])
                 (match V
                   [(-Vector αs) (-AΓ (list (-b (length αs))) Γ-ok)]
                   [_ (-AΓ (list '•) Γ-ok)]))
               (cons (list (-W 'vector? 'vector?) W)
                     (λ ([Γ-bad : -Γ])
                       (-AΓ (-blm l 'vector-length 'vector? (list V)) Γ-bad)))))]

    ;; Equality
    ['equal?
     (with-guarded-arity 2
       (match-define (list W₁ W₂) Ws)
       (match-define (-W V₁ e₁) W₁)
       (match-define (-W V₂ e₂) W₂)
       (define ans
         (match (or-R (V≡ V₁ V₂) (MσΓ⊢e M σ Γ (-?@ 'equal? e₁ e₂)))
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (-AΓ (list ans) Γ))]
    
    

    ;; Ariths
    ['add1
     (with-guarded-arity 1
       (match-define (list (and W (-W V ?e))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W) (ans-bad l 'add1 'number? V))))]

    ['sub1
     (with-guarded-arity 1
       (match-define (list (and W (-W V ?e))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W) (ans-bad l 'sub1 'number? V))))]
    
    ['+
     (with-guarded-arity 2
       (match-define (list (and W₁ (-W V₁ _)) (and W₂ (-W V₂ _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W₁) (ans-bad l '+ 'number? V₁))
               (cons (list -number?/W W₂) (ans-bad l '+ 'number? V₂))))]

    ['-
     (with-guarded-arity 2
       (match-define (list (and W₁ (-W V₁ _)) (and W₂ (-W V₂ _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W₁) (ans-bad l '- 'number? V₁))
               (cons (list -number?/W W₂) (ans-bad l '- 'number? V₂))))]

    ['*
     (with-guarded-arity 2
       (match-define (list (and W₁ (-W V₁ _)) (and W₂ (-W V₂ _))) Ws)
       (Γ+/-AΓ M σ Γ
               (λ ([Γ-ok : -Γ]) (-AΓ (list '•) Γ-ok))
               (cons (list -number?/W W₁) (ans-bad l '* 'number? V₁))
               (cons (list -number?/W W₂) (ans-bad l '* 'number? V₂))))]

    ))
|#

(: Γ+/- (∀ (X Y) -M -σ -Γ (-Γ → X) (Pairof (Listof -WV) (-Γ → Y)) *
           → (Values (Option X) (Setof Y))))
;; Refine the environment with sequence of propositions
;; and return (maybe) final sucessful environment
;; along with each possible failure
;; e.g. {} +/- ([num? n₁] [num? n₂]) -->
;;      (values {num? n₁, num? n₂} {{¬ num? n₁}, {num? n₁, ¬ num? n₂}})
(define (Γ+/- M σ Γ mk-ok . filters)
  (define-values (Γ-ok ans-bads)
    (for/fold ([Γ-ok : (Option -Γ) Γ]
               [ans-bads : (Setof Y) ∅])
              ([filt filters])
      (cond
        [Γ-ok
         (match-define (cons prop mk-bad) filt)
         (match-define (cons W-p W-vs) prop)
         (define-values (Γ-ok* Γ-bad*) (apply Γ+/-W∋Ws M σ Γ-ok W-p W-vs))
         (define ans-bads*
           (cond [Γ-bad* (set-add ans-bads (mk-bad Γ-bad*))]
                 [else ans-bads]))
         (values Γ-ok* ans-bads*)]
        [else (values #f ans-bads)])))
  (values (and Γ-ok (mk-ok Γ-ok)) ans-bads))

(: Γ+/-AΓ : -M -σ -Γ (-Γ → -AΓ) (Pairof (Listof -WV) (-Γ → -AΓ)) * → -AΓs)
(define (Γ+/-AΓ M σ Γ mk-ok . filters)
  (define-values (ans-ok ans-bads) (apply Γ+/- M σ Γ mk-ok filters))
  (cond [ans-ok (cond [(set-empty? ans-bads) ans-ok]
                      [else (set-add ans-bads ans-ok)])]
        [else ans-bads]))
