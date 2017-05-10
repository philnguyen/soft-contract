#lang racket

;; Populations of Automata

;; population-payoffs (-> [Listof Payoff])

;; match-up* (-> N Population)
;; (match-ups p r) matches up neighboring pairs of
;; automata in population p for r rounds 
;; 

;; death-birth N -> Population 
;; (death-birth p r) replaces r elements of p with r "children" of 
;; randomly chosen fittest elements of p, also shuffle 
;; constraint (< r (length p))

(provide
 ;; type Population
 
 ;; N -> Population
 ;; (build-population n c) for even n, build a population of size n 
 ;; with c constraint: (even? n)
 build-random-population
 
 )

;; =============================================================================
(require "automata.rkt" "utilities.rkt")

;; Population = (Cons Automaton* Automaton*)
;; Automaton* = [Vectorof Automaton]

(define DEF-COO 2)

;; -----------------------------------------------------------------------------
(define (build-random-population n)
  (define v (build-vector n (lambda (_) (make-random-automaton DEF-COO))))
  (new population% [a* v]))

(define population%
  (class object%
    (init-field a* (b* a*))
    (super-new)
    
    (define/public (payoffs)
      (for/list ([a a*]) (send a pay)))
    
    (define/public (match-up* rounds-per-match)
      ;; comment out this line if you want cummulative payoff histories:
      ;; see below in birth-death
      (reset)
      ;; -- IN --
      (for ([i (in-range 0 (- (vector-length a*) 1) 2)])
        (define p1 (vector-ref a* i))
        (define p2 (vector-ref a* (+ i 1)))
        (define-values (a1 a2) (send p1 match-pair p2 rounds-per-match))
        (vector-set! a* i a1)
        (vector-set! a* (+ i 1) a2))
      (void))
    
    (define/public (death-birth rate #:random (q #false))
      (define payoffs (for/list ([x (in-vector a*)]) (send x pay)))
      [define substitutes (choose-randomly payoffs rate #:random q)]
      (for ([i (in-range rate)][p (in-list substitutes)])
        (vector-set! a* i (send (vector-ref b* p) clone)))
      (shuffle-vector))
    
    ;; -> Void
    ;; effec: reset all automata in a*
    (define/private (reset)
      (for ([x a*][i (in-naturals)]) (vector-set! a* i (send x reset))))
    
    ;; -> Population
    ;; effect: shuffle vector b into vector a
    ;; constraint: (= (vector-length a) (vector-length b))
    ;; Fisher-Yates Shuffle
    
    (define/private (shuffle-vector)
      ;; copy b into a
      (for ([x (in-vector a*)][i (in-naturals)])
        (vector-set! b* i x))
      ;; now shuffle a 
      (for ([x (in-vector a*)] [i (in-naturals)])
        (define j (random (add1 i)))
        (unless (= j i) (vector-set! b* i (vector-ref b* j)))
        (vector-set! b* j x))
      (define tmp a*)
      (set! a* b*)
      (set! b* tmp)
      (void))))

;; -----------------------------------------------------------------------------

