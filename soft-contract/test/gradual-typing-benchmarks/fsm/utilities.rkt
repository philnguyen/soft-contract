#lang racket

;; Utility Functions


(provide
 sum
 relative-average
 choose-randomly)

;; =============================================================================

(define (sum l)
  (apply + l))


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
    (let loop  ([%s  %s])
      (cond
        [(< r (first %s)) 0]
        [else (add1 (loop (rest %s)))]))
    #;
    (for/last ([p (in-naturals)] [% (in-list %s)] #:final (< r %)) p)))

;; [Listof Probability] -> [Listof Probability]
;; calculate the accumulated probabilities 

(define (accumulated-%s probabilities)
  (define total (sum probabilities))
  (let relative->absolute
    ([payoffs  probabilities][so-far  #i0.0])
    (cond
      [(empty? payoffs) '()]
      [else (define nxt (+ so-far (first payoffs)))
            (cons
             (/ nxt total) (relative->absolute (rest payoffs) nxt))])))
