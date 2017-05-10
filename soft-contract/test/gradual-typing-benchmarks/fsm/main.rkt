#lang racket

;; Run a Simulation of Interacting Automata
(random-seed 7480)

;; =============================================================================
(require require-typed-check
 "automata.rkt"
 "population.rkt"
 "utilities.rkt")

;; effect run timed simulation, create and display plot of average payoffs
;; effect measure time needed for the simulation
(define (main)
   (simulation->lines
    (evolve (build-random-population 100) 1000 10 20))
   (void))

(define (simulation->lines data)
  (for/list 
    ([d  (in-list data)][n  (in-naturals)])
    (list n d)))

;; computes the list of average payoffs over the evolution of population p for
;; c cycles of of match-ups with r rounds per match and at birth/death rate of s
(define (evolve p c s r)
  (cond
    [(zero? c) '()]
    [else (define p2 (match-up* p r))
          ;; Note r is typed as State even though State is not exported 
          (define pp (population-payoffs p2))
          (define p3 (death-birth p2 s))
          ;; Note s same as r
          (cons
           (relative-average pp r)
           ;; Note evolve is assigned (-> ... [Listof Probability])
           ;; even though it is explicitly typed ... [Listof Payoff]
           (evolve p3 (- c 1) s r))]))

;; -----------------------------------------------------------------------------
(time (main))

