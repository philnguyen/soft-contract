#lang racket/base

(module+ test
  (require rackunit
           racket/match
           racket/contract
           racket/set
           "../../lang.rkt"
           (except-in "../../runtime.rkt" σ@)
           (only-in "../../provability.rkt" ⊢)
           (prefix-in ce: "../../ce/delta.rkt")
           (prefix-in ve: "../../verify/delta.rkt"))
  
  (define vns? .//?)
  
  (define/contract (σ@ σ i)
    (.σ? integer? . -> . .//?)
    (match-define (.σ m _) σ)
    (hash-ref m i))
  
  (define/contract (ans-same? Ans ans)
    (.Ans? vns? . -> . boolean?)
    (match-define (cons σ A) Ans)
    (match* (A ans)
      [((.L i) ans) (ans-same? (cons σ (σ@ σ i)) ans)]
      [((.// (? .•?) Cs) (.// (? .•?) Ds))
       (for/and ([D (in-set Ds)])
         (eq? '✓ (⊢ σ A D)))]
      [(_ _) (equal? A ans)]))
  
  (define/contract (check-ans-same? Ans ans)
    (.Ans? vns? . -> . any/c)
    (match-define (cons σ A) Ans)
    (match* (A ans)
      [((.L i) ans) (check-ans-same? (cons σ (σ@ σ i)) ans)]
      [((.// (? .•?) Cs) (.// (? .•?) Ds))
       (for ([D (in-set Ds)])
         (printf "σ:~n~a~nA:~n~a~nD:~n~a~n~n" σ A D)
         (check-equal? '✓ (⊢ σ A D)))]
      [(_ _) (check-equal? A ans)]))
  
  (define/contract (check-ans-include? Ans ans)
    (.Ans*? vns? . -> . any/c)
    (cond
      [(set? Ans)
       (check-true (for/or ([Ansᵢ (in-set Ans)])
                     (ans-same? Ansᵢ ans)))]
      [else (check-ans-same? Ans ans)]))
  
  (define/contract (ans-err? Ans)
    (.Ans? . -> . boolean?)
    (match Ans
      [(cons _ (.blm l _ _ _)) (equal? l 'tester)]
      [_ #f]))
  
  (define/contract (check-ans-err? Ans)
    (.Ans*? . -> . any/c)
    (cond
      [(set? Ans)
       (check-true (for/or ([Ansᵢ (in-set Ans)])
                     (ans-err? Ansᵢ)))]
      [else (match-define (cons _ A) Ans)
            (check-true (.blm? A))
            (match-define (.blm l _ _ _) A)
            (check-equal? l 'tester)]))
  
  (define/contract δ
    (parameter/c (.σ? .o? (listof .V?) symbol? . -> . (or/c (set/c .Ans?) .Ans?)))
    (make-parameter #f))
  (define/contract refine
    (parameter/c (.σ? .V? (or/c .V? (set/c .V?)) . -> . (cons/c .σ? .V?)))
    (make-parameter #f))
  
  (define (alloc Vs)
    ((listof .V?) . -> . (values .σ? (listof .V?)))
    (define-values (σ Vs-rev)
      (for/fold ([σ σ∅] [Vs-rev '()]) ([V (in-list Vs)])
        (match V
          [(.// (? .•?) Cs)
           (define-values (σ₁ L₁) (σ+ σ))
           (match-define (cons σ₂ L₂) ((refine) σ₁ L₁ Cs))
           (values σ₂ (cons L₂ Vs-rev))]
          [_ (values σ (cons V Vs-rev))])))
    (values σ (reverse Vs-rev)))
  
  (define/contract (check-δ o Vs expected-ans)
    (.o? (listof .V?) vns? . -> . any/c)
    (define-values (σ Vs′) (alloc Vs))
    (check-ans-include? ((δ) σ o Vs′ 'tester) expected-ans))
  
  (define/contract (check-δ-err o Vs)
    (.o? (listof .V?) . -> . any/c)
    (define-values (σ Vs′) (alloc Vs))
    (check-ans-err? ((δ) σ o Vs′ 'tester)))
  
  (define (● . Cs)
    (.// '• (list->set Cs)))
  
  (for ([-δ (list ce:δ ve:δ)]
        [-refine (list ce:refine ve:refine)])
    (parameterize ([δ -δ] [refine -refine])
      
      (check-δ 'number? (list (Prim 4.5)) (Prim #t))
      (check-δ 'number? (list (Prim "42")) (Prim #f))
      (check-δ 'number? (list (→V '•)) (Prim #t))
      (check-δ 'number? (list (→V '•)) (Prim #f))
      (check-δ 'number? (list (.// '• {set INT/C})) (Prim #t))
      (check-δ 'number? (list (.// '• {set STR/C})) (Prim #f))
      
      (check-δ-err '/ (list (Prim 4) (Prim 0)))
      (check-δ '/ (list (Prim 4) (Prim 7)) (Prim 4/7))
      (check-δ-err '/ (list (Prim 4) (.// '• {set REAL/C})))
      (check-δ '/ (list (Prim 4) (.// '• {set REAL/C})) (● REAL/C))
      (check-δ '/ (list (● INT/C POS/C) (● REAL/C NEG/C)) (● REAL/C NEG/C))
      (check-δ '/ (list (Prim 0) (● NUM/C)) (Prim 0))
      (check-δ-err '/ (list (Prim 0) (● NUM/C)))
      
      (check-δ '+ (list (● NUM/C) (● NUM/C)) (● NUM/C))
      (check-δ '+ (list (● REAL/C) (● INT/C)) (● REAL/C))
      (check-δ '+ (list (● INT/C) (● INT/C)) (● INT/C))
      (check-δ '+ (list (● POS/C INT/C) (● REAL/C POS/C)) (● REAL/C POS/C))
      (check-δ '+ (list (Prim 0) (● INT/C NON-NEG/C)) (● INT/C NON-NEG/C))
      
      (check-δ '- (list (● NUM/C) (● NUM/C)) (● NUM/C))
      (check-δ '- (list (● REAL/C) (● INT/C)) (● REAL/C))
      (check-δ '- (list (● INT/C) (Prim 42)) (● INT/C))
      (check-δ '- (list (● POS/C INT/C) (● NEG/C INT/C)) (● INT/C POS/C))
      (check-δ '- (list (● NON-NEG/C INT/C) (Prim -24)) (● INT/C NON-NEG/C))

      (check-δ 'expt (list (● REAL/C) (● REAL/C)) (● REAL/C))
      (check-δ-err 'expt (list (● REAL/C) (● REAL/C))))))


