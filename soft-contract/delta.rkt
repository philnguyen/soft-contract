#lang typed/racket/base
(require
 racket/match racket/set racket/bool racket/math
 "utils.rkt" "ast.rkt" "runtime.rkt" "provability.rkt"
 ;"make-delta.rkt"
 )
(provide (all-defined-out))

(: δ : -M -σ -Γ -o (Listof -WV) -src-loc → (Values -Δσ -AΓs))
;; Interpret primitive operations.
;; Return (Widened_Store × P((Result|Error)×Updated_Facts))
(define (δ M σ Γ o Ws loc)
  (match-define (-src-loc l pos) loc)
  
  (define-syntax-rule (with-guarded-arity n e ...)
    (cond
      [(= n (length Ws)) e ...]
      [else
       (values
        '()
        (-AΓ (-blm l (show-o o)
                   (-Clo '(x) (-@ '= (list (-x 'x) (-b n)) -Λ) -ρ⊥ -Γ⊤)
                   (WVs->Vs Ws))
             Γ))]))
  
  (match o
    ;; Primitive predicate
    [(? -pred?)
     (with-guarded-arity 1
       (match-define (list W) Ws)
       (define V_a
         (match (MσΓ⊢oW M σ Γ o W)
           ['✓ -tt]
           ['X -ff]
           [_ '•]))
       (values '() (-AΓ (list V_a) Γ)))]

    ;; Multiple values
    ['values (values '() (-AΓ (map (inst -W-x -V) Ws) Γ))]
    
    ['vector-length
     (with-guarded-arity 1
       (match-define (list W (-W V e)) Ws)
       (define-values (Γ-ok Γ-bad) (Γ+/-W∈W M σ Γ W (-W 'vector? 'vector?)))
       (define ans-bad (and Γ-bad (-AΓ (-blm l (show-o o) 'vector? (list V)) Γ-bad)))
       (define ans-ok
         (and Γ-ok
              (match V
                [(-Vector αs) (-AΓ (list (-b (length αs))) Γ-ok)]
                [_ (-AΓ (list '•) Γ-ok)])))
       (define ans
         (cond [(and ans-ok ans-bad) {set ans-ok ans-bad}]
               [ans-ok ans-ok]
               [else (assert ans-bad)]))
       (values '() ans))]

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
       (values '() (-AΓ (list ans) Γ)))]

    ;; Ariths
    ['+
     (with-guarded-arity 2
       (match-define (list W₁ W₂) Ws)
       (list W₁ W₂)
       (match-define (-W V₁ e₁) W₁)
       (match-define (-W V₂ e₂) W₂)
       (define ok-arg₁? (-?@ 'number? e₁))
       (define ok-arg₂? (-?@ 'number? e₂))
       (define Γ-bad₁ (Γ+ Γ (-not ok-arg₁?)))
       (define Γ-bad₂ (Γ+ Γ (-not ok-arg₂?)))
       (define Γ-ok   (Γ+ Γ ok-arg₁? ok-arg₂?))
       (define (blm-bad-arg [V : -V] [Γ : -Γ])
         (-AΓ (-blm l '+ 'number? (list V)) Γ))
       (define ans-ok   (-AΓ (list '•) Γ-ok))
       (define ans-bad₁ (blm-bad-arg V₁ Γ-bad₁))
       (define ans-bad₂ (blm-bad-arg V₂ Γ-bad₂))
       (define ans
         (match* ((MσΓ⊢oW M σ Γ 'number? W₁) (MσΓ⊢oW M σ Γ 'number? W₂))
           [('X _) ans-bad₁]
           [(_ 'X) ans-bad₂]
           [('✓ '✓) ans-ok]
           [('? '?) {set ans-bad₁ ans-bad₂ ans-ok}]
           [('? '✓) {set ans-bad₁ ans-ok}]
           [('✓ '?) {set ans-bad₂ ans-ok}]))
       (values '() ans))]
    
    ['-
     (with-guarded-arity 2
       (match-define (list W₁ W₂) Ws)
       (match-define (-W V₁ e₁) W₁)
       (match-define (-W V₂ e₂) W₂)
       (define ok-arg₁? (-?@ 'number? e₁))
       (define ok-arg₂? (-?@ 'number? e₂))
       (define Γ-bad₁ (Γ+ Γ (-not ok-arg₁?)))
       (define Γ-bad₂ (Γ+ Γ (-not ok-arg₂?)))
       (define Γ-ok   (Γ+ Γ ok-arg₁? ok-arg₂?))
       (define (blm-bad-arg [V : -V] [Γ : -Γ])
         (-AΓ (-blm l '- 'number? (list V)) Γ))
       (define ans-ok   (-AΓ (list '•) Γ-ok))
       (define ans-bad₁ (blm-bad-arg V₁ Γ-bad₁))
       (define ans-bad₂ (blm-bad-arg V₂ Γ-bad₂))
       (define ans
         (match* ((MσΓ⊢oW M σ Γ 'number? W₁) (MσΓ⊢oW M σ Γ 'number? W₂))
           [('X _) ans-bad₁]
           [(_ 'X) ans-bad₂]
           [('✓ '✓) ans-ok]
           [('? '?) {set ans-bad₁ ans-bad₂ ans-ok}]
           [('? '✓) {set ans-bad₁ ans-ok}]
           [('✓ '?) {set ans-bad₂ ans-ok}]))
       (values '() ans))]
    
    ['*
     (with-guarded-arity 2
       (match-define (list W₁ W₂) Ws)
       (match-define (-W V₁ e₁) W₁)
       (match-define (-W V₂ e₂) W₂)
       (define ok-arg₁? (-?@ 'number? e₁))
       (define ok-arg₂? (-?@ 'number? e₂))
       (define Γ-bad₁ (Γ+ Γ (-not ok-arg₁?)))
       (define Γ-bad₂ (Γ+ Γ (-not ok-arg₂?)))
       (define Γ-ok   (Γ+ Γ ok-arg₁? ok-arg₂?))
       (define (blm-bad-arg [V : -V] [Γ : -Γ])
         (-AΓ (-blm l '* 'number? (list V)) Γ))
       (define ans-ok   (-AΓ (list '•) Γ-ok))
       (define ans-bad₁ (blm-bad-arg V₁ Γ-bad₁))
       (define ans-bad₂ (blm-bad-arg V₂ Γ-bad₂))
       (define ans
         (match* ((MσΓ⊢oW M σ Γ 'number? W₁) (MσΓ⊢oW M σ Γ 'number? W₂))
           [('X _) ans-bad₁]
           [(_ 'X) ans-bad₂]
           [('✓ '✓) ans-ok]
           [('? '?) {set ans-bad₁ ans-bad₂ ans-ok}]
           [('? '✓) {set ans-bad₁ ans-ok}]
           [('✓ '?) {set ans-bad₂ ans-ok}]))
       (values '() ans))]
    ))

#|
(define-δ ; Identifiers `δ`, `σ`, `o`, `Vs`, and `l` are in scope
  [#:predicate number?]
  [#:predicate real?]
  [#:predicate integer?]
  [#:predicate not]
  [#:predicate boolean?]
  [#:predicate string?]
  [#:predicate symbol?]
  [#:predicate procedure?]
  [#:predicate keyword?]

  [#:predicate = : number? number?]
  [#:predicate < : real? real?]
  [#:predicate <= : real? real?]
  [#:predicate > : real? real?]
  [#:predicate >= : real? real?]
  [(add1 : [x : number?] → (∧ number? (=/c (+ x 1))))
   #:refinements
   (real? → real?)
   (integer? → integer?)
   ((>/c 0) → (>/c 0))]
  [(sub1 : [x : number?] → (∧ number? (=/c (- x 1))))
   #:refinements
   (real? → real?)
   (integer? → integer?)
   ((</c 0) → (</c 0))]
  [(+ : [x : number?] [y : number?] → (∧ number? (=/c (+ x y))))
   #:refinements
   (real? real? → real?)
   (integer? integer? → integer?)
   ((>/c 0) (≥/c 0) → (>/c 0))
   ((≥/c 0) (>/c 0) → (>/c 0))
   ((</c 0) (≤/c 0) → (</c 0))
   ((≤/c 0) (</c 0) → (</c 0))
   ((≥/c 0) (≥/c 0) → (≥/c 0))
   ((≤/c 0) (≤/c 0) → (≤/c 0))
   ((=/c 0) (=/c 0) → (=/c 0))
   ((=/c 0) any/c → (=/c y))
   (any/c (=/c 0) → (=/c x))]
  [(- : [x : number?] [y : number?] → (∧ number? (=/c (- x y))))
   #:refinements
   (real? real? → real?)
   (integer? integer? → integer?)
   ((>/c 0) (≤/c 0) → (>/c 0))
   ((</c 0) (≥/c 0) → (</c 0))
   ((≥/c 0) (≤/c 0) → (≥/c 0))
   ((≤/c 0) (≥/c 0) → (≤/c 0))
   ((=/c 0) (=/c 0) → (=/c 0))
   (any/c (=/c 0) → (=/c x))]
  [(* : [x : number?] [y : number?] → (∧ number? (=/c (* x y))))
   #:refinements
   (real? real? → real?)
   (integer? integer? → integer?)
   ((>/c 0) (>/c 0) → (>/c 0))
   ((</c 0) (</c 0) → (>/c 0))
   ((>/c 0) (</c 0) → (</c 0))
   ((</c 0) (>/c 0) → (</c 0))
   ((≥/c 0) (≥/c 0) → (≥/c 0))
   ((≤/c 0) (≤/c 0) → (≥/c 0))
   ((≤/c 0) (≥/c 0) → (≤/c 0))
   ((≥/c 0) (≤/c 0) → (≤/c 0))
   (any/c (=/c 0) → (=/c 0))
   ((=/c 0) any/c → (=/c 0))
   ((=/c 1) any/c → (=/c y))
   (any/c (=/c 1) → (=/c x))]
  [(/ : [x : number?] [y : (∧ number? (¬ (=/c 0)))] → (∧ number? (=/c (/ x y))))
   #:refinements
   (real? real? → real?)
   ((>/c 0) (>/c 0) → (>/c 0))
   ((</c 0) (</c 0) → (</c 0))
   ((>/c 0) (</c 0) → (</c 0))
   ((</c 0) (>/c 0) → (</c 0))
   ((≥/c 0) (≥/c 0) → (≥/c 0))
   ((≤/c 0) (≤/c 0) → (≥/c 0))
   ((≤/c 0) (≥/c 0) → (≤/c 0))
   ((≥/c 0) (≤/c 0) → (≤/c 0))
   ((=/c 0) any/c → (=/c 0))
   ((¬ (=/c 0)) any/c → (¬ (=/c 0)))
   (any/c (=/c 1) → (=/c x))]
  [(expt : [a : number?] [x : number?] → (∧ number? (=/c (expt a x))))
   #:other-errors
   [(=/c 0) (</c 0)]
   #:refinements
   (real? real? → real?)]
  ;; `quotient` and `remainder` don't work for now due to exactness
  #;[(quotient : [x : integer?] [y : (∧ integer? (¬ (=/c 0)))] → (∧ integer? (=/c (/ x y))))
   #:refinements
   ((≥/c 0) (>/c 0) → (≥/c 0))
   ((=/c 0) any/c → (=/c 0))]
  #;[(remainder : [x : integer?] [y : (∧ integer? (¬ (=/c 0)))] → (∧ integer? (=/c (remainder x y))))
   #:refinements
   ((≥/c 0) (>/c 0) → (≥/c 0))
   ((=/c 0) any/c → (=/c 0))]
  [(abs : [n : integer?] → integer?)
   #:refinements
   ((>/c 0) → (>/c 0))
   ((=/c 0) → (=/c 0))]
  [(round : [x : real?] → integer?)]
  [(floor : [x : real?] → integer?)]
  [(ceiling : [x : real?] → integer?)]
  [(log : [x : number?] → number?)]
  [(cos : [x : number?] → number?)]
  [(sin : [x : number?] → number?)]
  [(tan : [x : number?] → number?)]
  [(string-length : [s : string?] → (∧ integer? (≥/c 0))) #|FIXME update DSL to refine s|#]
  [#:predicate equal? : any/c any/c]

  ;; Temporary ops
  [(sqr : [x : number?] → number?)
   #:refinements
   (real? → (∧ real? (≥/c 0)))
   (integer? → integer?)]
  
  ;; Ugly stuff. Only Phil gets to use #:escape clauses
  [#:escape ; accessor
   {(and o (.st-ac t n i)) (list (and V (.// (.St t′ Vs) _)))}
   (cond [(equal? t t′) (cons σ (-Vs (list-ref Vs i)))]
         [else (cons σ (.blm l (name o) V (→V (.st-p t n))))])]
  [#:escape ; accessor on L
   {(and o (.st-ac t n i)) (list (.L α))}
   (match/Ans* (δ σ (.st-p t n) Vs 'Λ)
     [(cons σt (-Vs (.// (.b #t) _)))
      (match-define (.// (.St _ fields) _) (σ@ σt α))
      (cons σt (-Vs (list-ref fields i)))]
     [(cons σf (-Vs (.// (.b #f) _)))
      (cons σf (.blm l (name o) (.L α) (→V (.st-p t n))))])]
  [#:escape ; constructor
   {(and o (.st-mk t n)) Vs}
   (cond [(= n (length Vs)) (cons σ (-Vs (→V (.St t Vs))))]
         [else (cons σ (.blm l (name o) (Prim (length Vs)) (arity=/C n)))])]
  [#:escape ; struct predicate
   {(.st-p t n) (list V)}
   (define C (→V o))
   (match (⊢ σ V C)
     ['✓ (cons σ -VsTT)]
     ['X (cons σ -VsFF)]
     ['?
      (define-values (σt _t) (refine σ V C))
      (define-values (σf _f) (refine σ V (.¬/C C)))
      {set (cons σt -VsTT) (cons σf -VsFF)}])]
  [#:escape
   ((or 'arity=? 'arity>=? 'arity-includes?) (list V1 V2))
   (match/Ans* (δ σ 'procedure? (list V1) 'Λ)
     [(cons σt (-Vs (.// (.b #t) _)))
      (match/Ans* (δ σt 'integer? (list V2) 'Λ)
        [(cons σt (-Vs (.// (.b #t) _)))
         (match/nd: (.Vns → .Vnss) (check-C σt V1 (→C o #:2nd V2))
           [(cons σ V) (cons σ (-Vs V))])]
        [(cons σf (-Vs (.// (.b #f) _))) (cons σf (.blm l (name o) V2 INT/C))])]
     [(cons σf (-Vs (.// (.b #f) _))) (cons σf (.blm l (name o) V1 PROC/C))])]
  [#:escape ; multiple values
   {'values Vs} (cons σ (.Vs Vs))])
|#
