#lang racket

(define vec/c
  (->i ([msg (one-of/c 'x 'y 'add)])
       (res (msg)
            (match msg
              [(or 'x 'y) real?]
              ['add (vec/c . -> . vec/c)]))))

(define ext-vec/c
  (->i ([msg (one-of/c 'x 'y 'add 'len)])
       (res (msg)
            (match msg
              [(or 'x 'y) real?]
              ['add (vec/c . -> . vec/c)]
              ['len (and/c real? (>=/c 0))]))))

(define mixin/c ((real? real? . -> . vec/c) . -> . (real? real? . -> . ext-vec/c)))

(define (mk-vec x y)
  (match-lambda
    ['x x]
    ['y y]
    ['add (λ (v2) (mk-vec (+ x (v2 'x)) (+ y (v2 'y))))]))
(define/contract mk-vec/checked (real? real? . -> . vec/c) mk-vec)

(define (extend mk-vec)
  (λ (x y)
    (let ([v (mk-vec x y)])
      (match-lambda
        ['len (let ([x (v 'x)]
                    [y (v 'y)])
                (sqrt (+ (* x x) (* y y))))]
        [msg (v msg)]))))
(define/contract extend/checked mixin/c extend)

(define (bm mk-vec mixin [n 1000])
  (for ([i n])
    (let ([mk-ext-vec (mixin mk-vec)])
      ((mk-ext-vec (random) (random)) 'len))))

;; measure overhead of contracts
(time (bm mk-vec extend))
(time (bm mk-vec/checked extend/checked))