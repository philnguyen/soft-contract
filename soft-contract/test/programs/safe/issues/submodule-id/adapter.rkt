#lang racket/base

(module require/contracts racket/base
  (require soft-contract/fake-contract)
  (define g13 real?)
  (define g14 (or/c g13))
  (define g15 number?)
  (define g16 (or/c g15))
  (define g17 (lambda (x) (my-box? x)))
  (define l/1 (-> g14 (values g16)))
  (define l/35 (-> g14 (values g17)))
  (define l/37 (-> g17 (values g14)))
  (define absz #:opaque)
  (struct my-box (x) #:transparent)
  (provide (contract-out (absz l/1))
           (contract-out (struct my-box ((x g14))))))

(require 'require/contracts)
(provide absz (struct-out my-box))
