#lang typed/racket/base
(require racket/match racket/set racket/list racket/function
         "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt")
(provide all-prove? all-refute? some-proves? some-refutes?
         ⊢ Γ⊢ Γ⊢₀ Γ⊢ₑₓₜ σ⊢)

(:* all-prove? all-refute? some-proves? some-refutes? : -σ -Γ (Listof -W) -W → Boolean)
(define (all-prove?    σ Γ Ws W_p) (for/and ([W Ws]) (eq? (⊢ σ Γ W W_p) '✓)))
(define (all-refute?   σ Γ Ws W_p) (for/and ([W Ws]) (eq? (⊢ σ Γ W W_p) 'X)))
(define (some-proves?  σ Γ Ws W_p) (for/or  ([W Ws]) (eq? (⊢ σ Γ W W_p) '✓)))
(define (some-refutes? σ Γ Ws W_p) (for/or  ([W Ws]) (eq? (⊢ σ Γ W W_p) 'X)))

(: ⊢ : -σ -Γ -W -W → -R)
;; Check whether value `W_v` satisfies predicate `W_p` according to `σ` and `Γ`
(define (⊢ σ Γ W_v W_p)
  (match-define (-W V   π  ) W_v)
  (match-define (-W V_p π_p) W_p)
  (match (σ⊢ σ V V_p)
    ['? (if (and π π_p) (Γ⊢ Γ (-π@ π_p (list π))) '?)]
    [a a]))

(: Γ⊢ : -Γ -π* → -R)
;; Check whether syntax `π` always evaluates to non-#f value given assumptions `Γ`
(define (Γ⊢ Γ π)
  (match (Γ⊢₀ Γ π)
    ['? (if π ((Γ⊢ₑₓₜ) Γ π) '?)]
    [r r]))

;; Default (empty) external solver
(define Γ⊢ₑₓₜ : (Parameterof (-Γ -π → -R))
  (make-parameter
   (λ (Γ π)
     (error 'Internal "Uninitialized extended relation"))))

(: Γ⊢₀ : -Γ -π* → -R)
;; Internal simple proof system
(define (Γ⊢₀ Γ π*)

  (: go : -π → -R)
  (define (go π)
    (cond
      [(set-member? Γ π) '✓]
      [(set-member? Γ (-π@ 'false? (list π))) 'X]
      [else
       (match π
         [(-b #f) 'X]
         [(? -prim?) '✓]
         [(-π@ π πs)
          (match π ; TODO more sophisticated ones possible, e.g. (int? (+ _ _))
            ['integer?
             (match πs
               [(list (-b (? integer?))) '✓]
               [_ '?])]
            ['real?
             (match πs
               [(list (-b (? real?))) '✓]
               [_ '?])]
            ['number?
             (match πs
               [(list (-b (? number?))) '✓]
               [_ '?])]
            ['false? (¬R (Γ⊢₀ Γ (first πs)))]
            ['boolean?
             (match πs
               [(list (-b (? boolean?))) '✓]
               [_ '?])]
            ['string?
             (match πs
               [(list (-b (? string?))) '✓]
               [_ '?])]
            ['symbol?
             (match πs
               [(list (-b (? string?))) '✓]
               [_ '?])]
            ['procedure?
             (match πs
               [(list (-b _)) 'X]
               [_ '?])]
            ['keyword?
             '?]
            ;; TODO all the other ones
            [(or '+ '- '* '/) '✓]
            [_ '?])])]))

  (if π* (go π*) '?))

(: σ⊢ : -σ -V -V → -R)
(define (σ⊢ σ V C)
  (match* (V C)
    [((-b (? integer?)) 'integer?) '✓]
    [((-b (? real?)) 'real?) '✓]
    [((-b (? number?)) 'number?) '✓]
    [((? -λ↓?) 'procedure?) '✓]
    [((? -o?)  'procedure?) '✓]
    [((? -Ar?) 'procedure?) '✓]
    [((-St id _) (-st-p id _)) '✓]
    [((? -λ/C?) 'dep?) '✓]

    [('• (? -o?)) '?]
    [(_ (? -o?)) 'X]
    [(_ _) '?]))

#|
(: p⇒p : .pred .pred → -R)
(define (p⇒p p q)
  (cond
    [(equal? p q) '✓]
    [else
     (match* (p q)
       [((or 'true? 'false?) 'boolean?) '✓]
       [((or 'real? 'integer?) 'number?) '✓]
       [('integer? 'real?) '✓]
       [('boolean? (or 'true? 'false?)) '?]
       [('number? (or 'real? 'integer?)) '?]
       [('real? 'integer?) '?]
       [((-st-p t _) (-st-p t _)) '✓]
       [(_ _) 'X])]))
|#

(: ¬R : -R → -R)
(define ¬R
  (match-lambda ['✓ 'X] ['X '✓] [_ '?]))

(define-syntax ∨R
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['✓ '✓]
                    ['X (∨R e ...)]
                    ['? (match (∨R e ...) ['✓ '✓] [_ '?])])]))

(define-syntax ∧R
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e ...) (match e1
                    ['✓ (∧R e ...)]
                    ['X 'X]
                    ['? (match (∧R e ...) ['X 'X] [_ '?])])]))
(: decide-R : Boolean → -R)
(define decide-R (match-lambda [#t '✓] [#f 'X]))

