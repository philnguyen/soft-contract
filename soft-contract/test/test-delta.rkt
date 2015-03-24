#lang racket/base

(module+ test
  (require rackunit
           racket/match
           racket/contract
           racket/set
           racket/function
           racket/string
           "shared.rkt"
           "../lang.rkt"
           "../show.rkt"
           (except-in "../runtime.rkt" σ@)
           (only-in "../provability.rkt" ⊢)
           (prefix-in ce: "../ce/delta.rkt")
           (prefix-in ve: "../verify/delta.rkt"))
  
  (define vns? .//?)
  
  (define/contract (σ@ σ i)
    (.σ? integer? . -> . .//?)
    (match-define (.σ m _) σ)
    (hash-ref m i))
  
  ;; Allocate all • to labels
  (define/contract (alloc Vs)
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

  
  ;; Prepare for 2 versions of `δ` and `refine`
  (define/contract δ
    (parameter/c (.σ? .o? (listof .V?) symbol? . -> . (or/c (set/c .Ans?) .Ans?)))
    (make-parameter #f))
  (define/contract refine
    (parameter/c (.σ? .V? (or/c .V? (set/c .V?)) . -> . (cons/c .σ? .V?)))
    (make-parameter #f))

  ;; Apply `δ`
  (define/contract (@δ o Vs)
    (.o? (listof .V?) . -> . .Ans*?)
    (define-values (σ Vs′) (alloc Vs))
    (define Ans ((δ) σ o Vs′ 'tester))
    (printf "δ⟦~a, ~a⟧  ⟶  ~a~n"
            o
            (map (curry show-A σ∅) Vs)
            (cond [(set? Ans) (string-join (for/list ([Ansᵢ (in-set Ans)])
                                             (match-define (cons σ A) Ansᵢ)
                                             (format "~a" (show-A σ A)))
                                           ", "
                                           #:before-first "{ "
                                           #:after-last " }")]
                  [else (match-define (cons σ A) Ans)
                        (show-A σ A)]))
    Ans)
  
  ;; Check if `Ans` is subsumed by `ans`
  (define/contract (ans-same? Ans ans)
    (.Ans? vns? . -> . boolean?)
    (match-define (cons σ A) Ans)
    ;;(printf "ans-same? ~a : ~a~n" (show-A σ A) (show-A σ∅ ans))
    (match* (A ans)
      [((.L i) ans) (ans-same? (cons σ (σ@ σ i)) ans)]
      [((? .V? V) (.// (? .•?) Cs))
       (for/and ([C (in-set Cs)])
         ;;(printf "⊢ ~a : ~a~n" (show-A σ V) (show-A σ C))
         (eq? '✓ (⊢ σ V C)))]
      [(_ _) (equal? A ans)]))
  
  ;; Check if `Ans` is subsumed by `ans`
  (define/contract (check-ans-same? Ans ans)
    (.Ans? vns? . -> . any/c)
    (check-true (ans-same? Ans ans)))
  
  ;; Check if one of `Ans` is subsumed by `ans`
  (define/contract (check-ans-include? Ans ans)
    (.Ans*? vns? . -> . any/c)
    (cond
      [(set? Ans)
       (check-true (for/or ([Ansᵢ (in-set Ans)])
                     (ans-same? Ansᵢ ans)))]
      [else (check-ans-same? Ans ans)]))
  
  ;; Check if `Ans` is an error
  (define/contract (ans-err? Ans)
    (.Ans? . -> . boolean?)
    (match Ans
      [(cons _ (.blm l _ _ _)) (equal? l 'tester)]
      [_ #f]))
  
  ;; Check if `Ans` includes an error
  (define/contract (check-ans-err? Ans)
    (.Ans*? . -> . any/c)
    (cond
      [(set? Ans) (check-true (for/or ([Ansᵢ (in-set Ans)])
                                (ans-err? Ansᵢ)))]
      [else (match-define (cons _ A) Ans)
            (check-true (.blm? A))
            (match-define (.blm l _ _ _) A)
            (check-equal? l 'tester)]))
  
  ;; Check if expected answer is among those returned by `δ`
  (define/contract (check-δ o Vs expected)
    (.o? (listof .V?) vns? . -> . any/c)
    (check-ans-include? (@δ o Vs) expected))
  
  ;; Check if an error is among answers returned by `δ`
  (define/contract (check-δ-err o Vs)
    (.o? (listof .V?) . -> . any/c)
    (check-ans-err? (@δ o Vs)))
  
  ;; Check if `δ` gives no error
  (define/contract (check-δ-no-err o Vs)
    (.o? (listof .V?) . -> . any/c)
    (define Ans (@δ o Vs))
    (cond [(set? Ans) (check-false (for/or ([Ansᵢ (in-set Ans)])
                                     (.blm? (cdr Ansᵢ))))]
          [else (check-false (.blm? (cdr Ans)))]))
  
  ;; Check if `δ` gives only error
  (define/contract (check-δ-no-val o Vs)
    (.o? (listof .V?) . -> . any/c)
    (define Ans (@δ o Vs))
    (cond [(set? Ans) (check-false (for/or ([Ansᵢ (in-set Ans)])
                                     (.V? (cdr Ansᵢ))))]
          [else (check-false (.V? (cdr Ans)))]))
  
  ;; Check if `δ` gives only expected answer
  (define/contract (check-δ! o Vs expected)
    (.o? (listof .V?) vns? . -> . any/c)
    (define Ans (@δ o Vs))
    (cond [(set? Ans)
           (check-equal? (set-count Ans) 1)
           (check-ans-same? (set-first Ans) expected)]
          [else (check-ans-same? Ans expected)]))
  
  ;; Check if `δ` gives error and only error
  (define/contract (check-δ-err! o Vs)
    (.o? (listof .V?) . -> . any/c)
    (check-δ-err o Vs)
    (check-δ-no-val o Vs))
  
  (for ([-δ (list ce:δ ve:δ)]
        [-refine (list ce:refine ve:refine)])
    (parameterize ([δ -δ] [refine -refine])
      
      (check-δ! 'number? (list (Prim 4.5)) (Prim #t))
      (check-δ! 'number? (list (Prim "42")) (Prim #f))
      (check-δ 'number? (list (●)) (Prim #t))
      (check-δ 'number? (list (●)) (Prim #f))
      (check-δ! 'number? (list (● INT/C)) (Prim #t))
      (check-δ! 'number? (list (● STR/C)) (Prim #f))
      
      (check-δ-err! '/ (list (Prim 4) (Prim 0)))
      (check-δ! '/ (list (Prim 4) (Prim 7)) (Prim 4/7))
      (check-δ-err '/ (list (Prim 4) (● REAL/C)))
      (check-δ '/ (list (Prim 4) (● REAL/C)) (● REAL/C))
      (check-δ! '/ (list (● INT/C POS/C) (● REAL/C NEG/C)) (● REAL/C NEG/C))
      (check-δ '/ (list (Prim 0) (● NUM/C)) (Prim 0))
      (check-δ-err '/ (list (Prim 0) (● NUM/C)))
      
      (check-δ! '+ (list (● NUM/C) (● NUM/C)) (● NUM/C))
      (check-δ! '+ (list (● REAL/C) (● INT/C)) (● REAL/C))
      (check-δ! '+ (list (● INT/C) (● INT/C)) (● INT/C))
      (check-δ! '+ (list (● POS/C INT/C) (● REAL/C POS/C)) (● REAL/C POS/C))
      (check-δ! '+ (list (Prim 0) (● INT/C NON-NEG/C)) (● INT/C NON-NEG/C))
      
      (check-δ! '- (list (● NUM/C) (● NUM/C)) (● NUM/C))
      (check-δ! '- (list (● REAL/C) (● INT/C)) (● REAL/C))
      (check-δ! '- (list (● INT/C) (Prim 42)) (● INT/C))
      (check-δ! '- (list (● POS/C INT/C) (● NEG/C INT/C)) (● INT/C POS/C))
      (check-δ! '- (list (● NON-NEG/C INT/C) (Prim -24)) (● INT/C NON-NEG/C))
      
      (check-δ-no-err '< (list (● REAL/C) (● REAL/C)))
      (check-δ-err '< (list (● NUM/C) (● NUM/C)))
      (check-δ '< (list (● NUM/C) (● NUM/C)) (● BOOL/C))
      (check-δ! '< (list (Prim 42) (Prim 44)) (Prim #t))
      (check-δ! '< (list (Prim 42) (Prim 42)) (Prim #f))
      (check-δ! '< (list (● NON-POS/C) (● POS/C)) (Prim #t))
      (check-δ! '< (list (● NON-NEG/C) (● NEG/C)) (Prim #f))

      (check-δ 'expt (list (● REAL/C) (● REAL/C)) (● REAL/C))
      (check-δ-err 'expt (list (● REAL/C) (● REAL/C)))
      
      (check-δ 'string-length (list (●)) (● INT/C NON-NEG/C))
      (check-δ-err 'string-length (list (●)))
      (check-δ! 'string-length (list (● STR/C)) (● INT/C NON-NEG/C))
      (check-δ! 'string-length (list (Prim "hi")) (Prim 2))
      (check-δ-err! 'string-length (list (● (.¬/C STR/C)))))))
