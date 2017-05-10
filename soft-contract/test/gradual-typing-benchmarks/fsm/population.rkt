#lang racket

;; Populations of Automata

(provide
  build-random-population
  population-payoffs
  match-up*
  death-birth
  ;; == 
)

;; =============================================================================
(require require-typed-check
 "automata.rkt"
 "utilities.rkt"
)

;; Population = (Cons Automaton* Automaton*)
;; Automaton* = [Vectorof Automaton]

(define DEF-COO 2)

;; -----------------------------------------------------------------------------
(define (build-random-population n)
  (define v (build-vector n (lambda (_) (make-random-automaton DEF-COO))))
  (cons v v))

;; -----------------------------------------------------------------------------
(define (population-payoffs population0)
  (define population (car population0))
  (for/list ([a population]) (automaton-payoff a)))

;; -----------------------------------------------------------------------------

(define (match-up* population0 rounds-per-match)
  (define a* (car population0))
  ;; comment out this line if you want cummulative payoff histories:
  ;; see below in birth-death
  (population-reset a*)
  ;; -- IN --
  (for ([i (in-range 0 (- (vector-length a*) 1) 2)])
    (define p1 (vector-ref a* i))
    (define p2 (vector-ref a* (+ i 1)))
    (define-values (a1 a2) (match-pair p1 p2 rounds-per-match))
    (vector-set! a* i a1)
    (vector-set! a* (+ i 1) a2))
  population0)

;; effec: reset all automata in a*
(define (population-reset a*)
  (for ([x (in-vector a*)][i (in-naturals)])
    (vector-set! a* i (automaton-reset x))))

;; -----------------------------------------------------------------------------

(define (death-birth population0 rate #:random (q #false))
  (match-define (cons a* b*) population0)
  (define payoffs
    (for/list  ([x  (in-vector a*)])
      (automaton-payoff x)))
  [define substitutes (choose-randomly payoffs rate #:random q)]
  (for ([i (in-range rate)][p (in-list substitutes)])
    (vector-set! a* i (clone (vector-ref b* p))))
  (shuffle-vector a* b*))

;; effect: shuffle vector b into vector a
;; constraint: (= (vector-length a) (vector-length b))
;; Fisher-Yates Shuffle

(define (shuffle-vector b a)
  ;; copy b into a
  (for ([x (in-vector b)][i (in-naturals)])
    (vector-set! a i x))
  ;; now shuffle a 
  (for ([x (in-vector b)] [i (in-naturals)])
    (define j (random (add1 i)))
    (unless (= j i) (vector-set! a i (vector-ref a j)))
    (vector-set! a j x))
  (cons a b))
