#lang typed/racket/base
(require
 racket/match racket/set racket/bool racket/math
 "utils.rkt" "lang.rkt" "runtime.rkt" "show.rkt" "provability.rkt"
 ;"make-delta.rkt"
 )
(provide (all-defined-out))

(: δ : -σ -Γ -o -WVs Mon-Party → (Values -σ -AΓs))
;; Interpret primitive operations.
;; Return (Widened_Store × P((Result|Error)×Updated_Facts))
(define (δ σ Γ o Ws l)
  (match o
    ;; Primitive predicate
    [(? -pred? o)
     (match Ws
       [(list (and W (-W V π)))
        (match (⊢ σ Γ W (-W o o))
          ['✓ (values σ (-AΓ -True/Vs Γ))]
          ['X (values σ (-AΓ -False/Vs Γ))]
          ['?
           (define π-tt (-π@* o (list π)))
           (values σ {set (-AΓ -True/Vs (Γ+ Γ π-tt))
                          (-AΓ -False/Vs (Γ+ Γ (-π@* 'false? (list π-tt))))})])]
       [_ (values
           σ
           (-AΓ (-blm l (show-o o)
                      (-Clo '(x) (-@ '= (list (-x 'x) (-b 1)) 'Λ) -ρ∅ -Γ∅)
                      (WVs->Vs Ws))
                Γ))])]
    
    ;; Constructor
    [(-st-mk id n)
     (cond
       [(= n (length Ws))
        (define αs (alloc-fields Γ o Ws))
        (define σ* : -σ
          (for/fold ([σ* σ]) ([α αs] [W Ws])
            (⊔ σ α (-W-x W))))
        (values σ* (-AΓ (list (-St id αs)) Γ))]
       [else
        (values
         σ
         (-AΓ (-blm l (show-o o)
                    (-Clo '(x) (-@ '= (list (-x 'x) (-b 1)) 'Λ) -ρ∅ -Γ∅)
                    (WVs->Vs Ws))
              Γ))])]
    
    ;; Accessor
    [(-st-ac id n i)
     (match Ws
       [(list (and W (-W V π)))
        (define-values (_ AΓs) (δ σ Γ (-st-p id n) Ws 'Λ))
        (define π_a (-π@* o (list π)))
        (define AΓs*
          (match/nd: (-AΓ → -AΓ) AΓs
           [(-AΓ (-b #t) Γ_t)
            (match V
              [(-St _ αs)
               (match/nd: (-V → -AΓ) (hash-ref σ (list-ref αs i))
                 [V (-AΓ V Γ_t)])]
              [_ (-AΓ '• Γ_t)])]
          [(-AΓ (-b #f) Γ_f)
           (-AΓ (-blm l (show-o o) (-st-p id n) Ws) Γ_f)]))
        (values σ AΓs*)]
       [_ (values
           σ
           (-AΓ (-blm l (show-o o)
                      (-Clo '(x) (-@ '= (list (-x 'x) (-b 1)) 'Λ) -ρ∅ -Γ∅)
                      (WVs->Vs Ws))
                 Γ))])]

    ;; Ariths
    ['+
     (match Ws
       [(list W₁ W₂)
        (define-values (_σ₁ AΓs₁) (δ σ Γ 'number? (list W₁) 'Λ))

        (define AΓs₂
          (match/nd: (-AΓ → -AΓ) AΓs₁
            [(-AΓ (list (-b #t)) Γ₁)
             (define-values (_σ₂ AΓs₂)
               (δ σ Γ₁ 'number? (list W₂) 'Λ))
             AΓs₂]
            [(-AΓ (list (-b #f)) Γ₁)
             (-AΓ (-blm l o 'number? (list (-W-x W₁))) Γ₁)]))
        
        (values
         σ
         (match/nd: (-AΓ → -AΓ) AΓs₂
          [(and a (-AΓ (? -blm?) _)) a]
          [(-AΓ (list (-b #t)) Γ₂)
           (match* ((-W-x W₁) (-W-x W₂))
             [((-b (? number? x)) (-b (? number? y)))
              (-AΓ (list (-b (+ x y))) Γ₂)]
             [(_ _) (-AΓ (list '•) Γ₂)])]
          [(-AΓ (list (-b #f)) Γ₂)
           (-AΓ (-blm l o 'number? (list (-W-x W₂))) Γ₂)]))]
       [_
        (values
         σ
         (-AΓ (-blm l (show-o o)
                    (-Clo '(x) (-@ '= (list (-x 'x) (-b 2)) 'Λ) -ρ∅ -Γ∅)
                    (WVs->Vs Ws))
              Γ))])]
    
    ['-
     (match Ws
       [(list W₁ W₂)
        (define-values (_σ₁ AΓs₁) (δ σ Γ 'number? (list W₁) 'Λ))

        (define AΓs₂
          (match/nd: (-AΓ → -AΓ) AΓs₁
            [(-AΓ (list (-b #t)) Γ₁)
             (define-values (_σ₂ AΓs₂)
               (δ σ Γ₁ 'number? (list W₂) 'Λ))
             AΓs₂]
            [(-AΓ (list (-b #f)) Γ₁)
             (-AΓ (-blm l o 'number? (list (-W-x W₁))) Γ₁)]))
        
        (values
         σ
         (match/nd: (-AΓ → -AΓ) AΓs₂
          [(and a (-AΓ (? -blm?) _)) a]
          [(-AΓ (list (-b #t)) Γ₂)
           (match* ((-W-x W₁) (-W-x W₂))
             [((-b (? number? x)) (-b (? number? y)))
              (-AΓ (list (-b (- x y))) Γ₂)]
             [(_ _) (-AΓ (list '•) Γ₂)])]
          [(-AΓ (list (-b #f)) Γ₂)
           (-AΓ (-blm l o 'number? (list (-W-x W₂))) Γ₂)]))]
       [_
        (values
         σ
         (-AΓ (-blm l (show-o o)
                    (-Clo '(x) (-@ '= (list (-x 'x) (-b 2)) 'Λ) -ρ∅ -Γ∅)
                    (WVs->Vs Ws))
              Γ))])]

    ['*
     (match Ws
       [(list W₁ W₂)
        (define-values (_σ₁ AΓs₁) (δ σ Γ 'number? (list W₁) 'Λ))

        (define AΓs₂
          (match/nd: (-AΓ → -AΓ) AΓs₁
            [(-AΓ (list (-b #t)) Γ₁)
             (define-values (_σ₂ AΓs₂)
               (δ σ Γ₁ 'number? (list W₂) 'Λ))
             AΓs₂]
            [(-AΓ (list (-b #f)) Γ₁)
             (-AΓ (-blm l o 'number? (list (-W-x W₁))) Γ₁)]))
        
        (values
         σ
         (match/nd: (-AΓ → -AΓ) AΓs₂
          [(and a (-AΓ (? -blm?) _)) a]
          [(-AΓ (list (-b #t)) Γ₂)
           (match* ((-W-x W₁) (-W-x W₂))
             [((-b (? number? x)) (-b (? number? y)))
              (-AΓ (list (-b (* x y))) Γ₂)]
             [(_ _) (-AΓ (list '•) Γ₂)])]
          [(-AΓ (list (-b #f)) Γ₂)
           (-AΓ (-blm l o 'number? (list (-W-x W₂))) Γ₂)]))]
       [_
        (values
         σ
         (-AΓ (-blm l (show-o o)
                    (-Clo '(x) (-@ '= (list (-x 'x) (-b 2)) 'Λ) -ρ∅ -Γ∅)
                    (WVs->Vs Ws))
              Γ))])]))

(: alloc-fields : -Γ -o -WVs → (Listof -α))
;; Allocate a list of addresses for given fields in a constructor
(define (alloc-fields Γ o Ws)
  
  (: alloc-field : Integer -WV → -α)
  (define (alloc-field i W)
    (log-warning "alloc-field: TODO proper implementation")
    (match-define (-W V π) W)
    (cond
      [π (alloc o π Γ i)]
      [else (alloc o Γ i)]))
  
  (for/list ([i (in-naturals)] [W Ws]) (alloc-field i W)))

#|
(define-δ ; Identifiers `δ`, `σ`, `o`, `Vs`, and `l` are in scope
  [#:predicate number?]
  [#:predicate real?]
  [#:predicate integer?]
  [#:predicate false?]
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
