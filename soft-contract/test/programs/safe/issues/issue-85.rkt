#lang racket

(define (f x)
  (cond
    [(exn:fail? x) (exn? x)]     ; test implication
    [(exn? x) (not (number? x))] ; test exclusion
    [else #t]))

(define (g x) (number? (make-immutable-hash x)))

(provide
 (contract-out
  [f (any/c . -> . values)]
  [g ((listof pair?) . -> . not)]
  ))
