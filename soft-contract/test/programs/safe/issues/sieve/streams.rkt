#lang racket/base

(require racket/contract)
(define g15 exact-nonnegative-integer?)
(define g16 (or/c g15))
(define g17 (lambda (x) (stream? x)))
(define g18 (-> g17))
(define g19 struct-type?)
(define g20 (λ (_) #f))
(define g21 any/c)
(define g22 '#t)
(define g23 '#f)
(define g24 (or/c g22 g23))
(define g25 (-> g21 (values g24)))
(define g26 (or/c g20 g25))
(define g27 (-> (values g17)))
(define g28 (listof g16))
(define generated-contract5 (-> g16 g18 (values g17)))
(define generated-contract6 g19)
(define generated-contract7 g26)
(define generated-contract8 (-> g17 (values g27)))
(define generated-contract9 (-> g17 (values g16)))
(define generated-contract11 (-> g16 g18 (values g17)))
(define generated-contract12 (-> g17 g16 (values g16)))
(define generated-contract13 (-> g17 g16 (values g28)))
(define generated-contract14 (-> g17 (values g16 g17)))
(module require/contracts racket/base
  (require soft-contract/fake-contract)
  (provide))
(require (prefix-in -: (only-in 'require/contracts))
         (except-in 'require/contracts))

(struct stream (first rest))

(define (make-stream hd thunk) (stream hd thunk))

(define (stream-unfold st) (values (stream-first st) ((stream-rest st))))

(define (stream-get st i)
  (define-values (hd tl) (stream-unfold st))
  (cond ((= i 0) hd) (else (stream-get tl (sub1 i)))))

(define (stream-take st n)
  (cond
    ((= n 0) '())
    (else
     (define-values (hd tl) (stream-unfold st))
     (cons hd (stream-take tl (sub1 n))))))

(provide (contract-out (stream-take generated-contract13))
         (contract-out (stream-get generated-contract12))
         (contract-out (stream-unfold generated-contract14))
         (contract-out (make-stream generated-contract5))
         (contract-out (struct stream ((first g16) (rest g18)))))
