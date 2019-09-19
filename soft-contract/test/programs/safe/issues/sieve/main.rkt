#lang racket/base

(require racket/contract)
(module require/contracts racket/base
  (require (only-in soft-contract/fake-contract)
           "streams.rkt"
           racket/contract)
  (define g14 exact-nonnegative-integer?)
  (define g15 (or/c g14))
  (define g16 (lambda (x) (stream? x)))
  (define g17 (-> (values g16)))
  (define g18 (-> g16))
  (define g19 (listof g15))
  (define l/33 (-> g15 g17 (values g16)))
  (define l/35 (-> g16 (values g15)))
  (define l/37 (-> g16 (values g18)))
  (define l/39 (-> g15 g17 (values g16)))
  (define l/41 (-> g16 (values g15 g16)))
  (define l/43 (-> g16 g15 (values g15)))
  (define l/45 (-> g16 g15 (values g19)))
  (provide l/43
           l/35
           l/41
           g14
           g15
           g16
           g17
           l/33
           l/39
           g18
           l/37
           g19
           l/45
           (contract-out (stream-get l/43))
           (contract-out (stream-take l/45))
           (contract-out (make-stream l/39))
           (contract-out (stream-unfold l/41))
           (contract-out (struct stream ((first g15) (rest g17))))))
(require (prefix-in
          -:
          (only-in
           'require/contracts
           stream-unfold
           make-stream
           stream-take
           stream-get
           stream?))
         (except-in
          'require/contracts
          stream-unfold
          make-stream
          stream-take
          stream-get
          stream?))
(define-values
  (stream-unfold make-stream stream-take stream-get stream?)
  (values
   -:stream-unfold
   -:make-stream
   -:stream-take
   -:stream-get
   -:stream?))
(require require-typed-check)

(define (count-from n) (make-stream n (lambda () (count-from (add1 n)))))

(define (sift n st)
  (define-values (hd tl) (stream-unfold st))
  (cond
    ((= 0 (modulo hd n)) (sift n tl))
    (else (make-stream hd (lambda () (sift n tl))))))

(define (sieve st)
  (define-values (hd tl) (stream-unfold st))
  (make-stream hd (lambda () (sieve (sift hd tl)))))

(define primes (sieve (count-from 2)))

(define N-1 600)

(define (main) (void (stream-get primes N-1)))
(time (main))
