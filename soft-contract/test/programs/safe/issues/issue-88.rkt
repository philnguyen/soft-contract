#lang racket

(define (f x)
  (match x
    ((list null null) #false)
    (_ #true)))

(provide (contract-out (f (-> (listof integer?) boolean?))))
