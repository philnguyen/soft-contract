#lang racket

;; Utility Functions

(provide
 ;; [Listof Number] -> Number 
 sum
 
 ;; [Listof Number] Number -> Number 
 relative-average
 
 ;; type Probability = NonNegativeReal 
 ;; [Listof Probability] N -> [Listof N]
 ;; choose n random indices i such i's likelihood is (list-ref probabilities i)
 choose-randomly)

;; =============================================================================
(define (sum l)
  (apply + l))

;; -----------------------------------------------------------------------------
(define (relative-average l w)
  (exact->inexact
   (/ (sum l)
      w (length l))))

;; -----------------------------------------------------------------------------

(define (choose-randomly probabilities speed #:random (q #false))
  (define %s (accumulated-%s probabilities))
  (for/list ([n (in-range speed)])
    [define r (or q (random))]
    ;; population is non-empty so there will be some i such that ... 
    (for/last ([p (in-naturals)] [% (in-list %s)] #:final (< r %)) p)))

;; [Listof Probability] -> [Listof Probability]
;; calculate the accumulated probabilities 

(define (accumulated-%s probabilities)
  (define total (sum probabilities))
  (let relative->absolute ([payoffs probabilities][so-far #i0.0])
    (cond
      [(empty? payoffs) '()]
      [else (define nxt (+ so-far (first payoffs)))
            (cons (/ nxt total) (relative->absolute (rest payoffs) nxt))])))
