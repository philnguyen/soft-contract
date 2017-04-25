#lang racket

(provide/contract
 [f (-> any/c)])

(define f 
  (let ([x -3])
    (λ ()
      (set! x (+ 1 x))
      (/ 1 x))))
