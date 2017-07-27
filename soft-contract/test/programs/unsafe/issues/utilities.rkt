#lang racket

(define (sum l)
  (apply + l))

(define (relative-average l w)
  (exact->inexact (/ (sum l) w (length l))))

(define (choose-randomly probabilities speed q)
  (define %s (accumulated-%s probabilities))
  (for/list ([n (in-range speed)])
    (define r (or q (random)))
    (let loop ([%s %s])
      (cond [(< r (first %s)) 0]
            [else (add1 (loop (rest %s)))])))
  )

(define (accumulated-%s probabilities)
  (define total (sum probabilities))
  (let relative->absolute ((payoffs probabilities) (so-far 0.0))
    (cond [(empty? payoffs) (quote ())]
          [else (define nxt (+ so-far (first payoffs)))
                (cons (/ nxt total)
                      (relative->absolute (rest payoffs) nxt))])))

(require racket/contract)
(provide (contract-out
  (relative-average (-> (listof real?) real? real?))
))
