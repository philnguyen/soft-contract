#lang racket

(provide/contract
 [box/c any/c]
 [box (any/c . -> . box/c)]
 [set-box! (box/c any/c . -> . any/c)]
 [unbox (box/c . -> . any/c)])

(define box/c
  ;; This is unneccessary, as the interface exports `set-box!` and `unbox` instead
  ;; But whatever
  (->i ([msg (one-of/c 'set-box! 'unbox)])
       (res (msg)
            (case msg
              [(set-box!) (any/c . -> . void?)]
              [(unbox) any/c]))))

(define (box v)
  (let ([x v])
    (λ (msg)
      (case msg
        [(set-box!) (λ (w) (set! x w))]
        [(unbox) x]))))

(define (set-box! b v) ((b 'set-box!) v))
(define (unbox b) (b 'unbox))
