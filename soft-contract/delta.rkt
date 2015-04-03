#lang typed/racket/base
(require
 racket/match racket/set racket/bool
 "utils.rkt" "lang.rkt" "runtime.rkt" "provability.rkt" "make-delta.rkt")
(provide (all-defined-out)
         (except-out (all-from-out "make-delta.rkt") define-δ))

(define-δ ; Identifiers `δ`, `σ`, `o`, `Vs`, and `l` are in scope
  [#:predicate number?]
  [#:predicate real?]
  [#:predicate integer?]
  [#:predicate false?]
  [#:predicate boolean?]
  [#:predicate string?]
  [#:predicate symbol?]
  [#:predicate procedure?]

  [#:predicate = : number? number?]
  [#:predicate < : real? real?]
  [#:predicate <= : real? real?]
  [#:predicate > : real? real?]
  [#:predicate >= : real? real?]
  [(add1 : [x : number?] → (∧ number? (=/c (+ 1 x))))
   #:refinements
   (real? → real?)
   (integer? → integer?)
   ((>/c 0) → (>/c 0))]
  [(sub1 : [x : number?] → (∧ number? (=/c (+ 1 x))))
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
   (any/c (=/c 1) → (=/c x))]
  [(expt : [a : number?] [x : number?] → (∧ number? (=/c (expt a x))))
   #:other-errors
   [(=/c 0) (</c 0)]
   #:refinements
   (real? real? → real?)]
  [(quotient : [x : integer?] [y : (∧ integer? (¬ (=/c 0)))] → (∧ integer? (=/c (/ x y))))
   #:refinements
   ((≥/c 0) (>/c 0) → (≥/c 0))
   ((=/c 0) any/c → (=/c 0))]
  [(remainder : [x : integer?] [y : (∧ integer? (¬ (=/c 0)))] → (∧ integer? (=/c (remainder x y))))
   #:refinements
   ((≥/c 0) (>/c 0) → (≥/c 0))
   ((=/c 0) any/c → (=/c 0))]
  [(abs : [n : integer?] → (∧ integer? (=/c (abs n))))
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
  
  ;; Ugly stuff. Only Phil gets to use #:escape clauses
  [#:escape ; accessor
   {(.st-ac t n i) (list (and V (.// (.St t′ Vs) _)))}
   (cond [(equal? t t′) (cons σ (list-ref Vs i))]
         [else (cons σ (.blm l (format "~a" #|hack|# t) V (→V (.st-p t n))))])]
  [#:escape ; constructor
   {(.st-mk t n) Vs}
   (cond [(= n (length Vs)) (cons σ (→V (.St t Vs)))]
         [else (cons σ (.blm l (format "~a" #|hack|# t) (Prim (length Vs)) (arity=/C n)))])]
  [#:escape ; struct predicate
   {(.st-p t n) (list V)}
   (define C (→V o))
   (match (⊢ σ V C)
     ['✓ (cons σ TT)]
     ['X (cons σ FF)]
     ['?
      (match-define (cons σt _) (refine σ V C))
      (match-define (cons σf _) (refine σ V (.¬/C C)))
      {set (cons σt TT) (cons σf FF)}])]
  [#:escape
   ((or 'arity=? 'arity>=? 'arity-includes?) (list V1 V2))
   (match/Ans* (δ σ 'procedure? (list V1) 'Λ)
     [(cons σt (.// (.b #t) _))
      (match/Ans* (δ σt 'integer? (list V2) 'Λ)
        [(cons σt (.// (.b #t) _)) (check-C σt V1 (→C o #:2nd V2))]
        [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V2 INT/C))])]
     [(cons σf (.// (.b #f) _)) (cons σf (.blm l (name o) V1 PROC/C))])])
