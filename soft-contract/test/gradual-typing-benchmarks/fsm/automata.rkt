#lang racket

;; An N-states, N-inputs Automaton

(provide
 defects
 cooperates
 tit-for-tat
 grim-trigger
 make-random-automaton
 match-pair
 automaton-reset
 clone
 automaton-payoff
 ;; --
 automaton?
)

;; -----------------------------------------------------------------------------
(define COOPERATE 0)
(define DEFECT    1)

(struct automaton (current
                   original
                   payoff
                   table)
                   #:transparent)

(define (make-random-automaton n)
  (define (transitions _i) (build-vector n (lambda (_) (random n))))
  (define original-current (random n))
  (automaton original-current original-current 0 (build-vector n transitions)))

(define (make-automaton current table)
  (automaton current current 0 table))

(define (transitions #:i-cooperate/it-cooperates cc
                     #:i-cooperate/it-defects    cd
                     #:i-defect/it-cooperates    dc
                     #:i-defect/it-defects       dd)
  (vector (vector cc cd)
          (vector dc dd)))

;; CLASSIC AUTOMATA
;; the all defector has 2 states of cooperate and defect
;; but it always defects, no matter what
;; the opponent may play cooperate or defect
;; it doesnt care, it always stay in the state defect

(define defect-transitions
  (transitions #:i-cooperate/it-cooperates DEFECT 
               #:i-cooperate/it-defects    DEFECT
               #:i-defect/it-cooperates    DEFECT
               #:i-defect/it-defects       DEFECT))

(define (defects p0)
  (automaton DEFECT DEFECT p0 defect-transitions))

(define cooperates-transitions
  (transitions #:i-cooperate/it-cooperates COOPERATE 
               #:i-cooperate/it-defects    COOPERATE
               #:i-defect/it-cooperates    COOPERATE
               #:i-defect/it-defects       COOPERATE))

(define (cooperates p0)
  (automaton COOPERATE COOPERATE p0 cooperates-transitions))

;; the tit for tat starts out optimistic, it cooperates initially
;; however, if the opponent defects, it punishes by switching to defecting
;; if the opponent cooperates, it returns to play cooperate again

(define tit-for-tat-transitions
  (transitions #:i-cooperate/it-cooperates COOPERATE 
               #:i-cooperate/it-defects    DEFECT
               #:i-defect/it-cooperates    COOPERATE
               #:i-defect/it-defects       DEFECT))


(define (tit-for-tat p0)
  (automaton COOPERATE COOPERATE p0 tit-for-tat-transitions))

;; the grim trigger also starts out optimistic,
;; but the opponent defects for just once then
;; it jumps to defect forever
;; it doesnt forgive, and doesnt forget

(define grim-transitions
  (transitions #:i-cooperate/it-cooperates COOPERATE 
               #:i-cooperate/it-defects    DEFECT
               #:i-defect/it-cooperates    DEFECT
               #:i-defect/it-defects       DEFECT))

(define (grim-trigger p0)
  (automaton COOPERATE COOPERATE p0 grim-transitions))

(define (automaton-reset a)
  (match-define (automaton current c0 payoff table) a)
  (automaton c0 c0 0 table))

(define (clone a)
  (match-define (automaton current c0 payoff table) a)
  (automaton c0 c0 0 table))

;; -----------------------------------------------------------------------------
;; the sum of pay-offs for the two respective automata over all rounds

(define (match-pair auto1 auto2 rounds-per-match)
  (match-define (automaton current1 c1 payoff1 table1) auto1)
  (match-define (automaton current2 c2 payoff2 table2) auto2)
  (define-values (new1 p1 new2 p2)
    (for/fold ([current1  current1]
               [payoff1  payoff1]
               [current2  current2]
               [payoff2  payoff2])
              ([_ (in-range rounds-per-match)])
      (match-define (cons p1 p2) (payoff current1 current2))
      (define n1 (vector-ref (vector-ref table1 current1) current2))
      (define n2 (vector-ref (vector-ref table2 current2) current1))
      (values n1 (+ payoff1 p1) n2 (+ payoff2 p2))))
  (values (automaton new1 c1 p1 table1) (automaton new2 c2 p2 table2)))

;; -----------------------------------------------------------------------------
;; PayoffTable = [Vectorof k [Vectorof k (cons Payoff Payoff)]]
(define PAYOFF-TABLE
  (vector (vector (cons 3 3) (cons 0 4))
          (vector (cons 4 0) (cons 1 1))))

(define (payoff current1 current2)
  (vector-ref (vector-ref PAYOFF-TABLE current1) current2))
