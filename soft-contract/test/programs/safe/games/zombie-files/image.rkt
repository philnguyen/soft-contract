#lang racket/base

(require racket/contract)
(define g13 real?)
(define g14 (or/c g13))
(define g15 string?)
(define g16 (lambda (x) (image? x)))
(define g17 any/c)
(define g18 struct-type?)
(define g19 (λ (_) #f))
(define g20 '#t)
(define g21 '#f)
(define g22 (or/c g20 g21))
(define g23 (-> g17 (values g22)))
(define g24 (or/c g19 g23))
(define g25 any/c)
(define generated-contract5 (-> g14 g15 g15 (values g16)))
(define generated-contract6 (-> g14 g14 (values g16)))
(define generated-contract7 g18)
(define generated-contract8 g24)
(define generated-contract9 (-> g16 (values g25)))
(define generated-contract11 (-> g17 (values g16)))
(define generated-contract12 (-> g16 g14 g14 g16 (values g16)))

(struct image (impl))

(define (empty-scene w h)
  (when (or (negative? w) (negative? h))
    (error 'image "Arguments must be non-negative real numbers"))
  (image (cons w h)))

(define (place-image i1 w h i2) (image (list i1 w h i2)))

(define (circle radius style color) (image (list radius style color)))

(provide (contract-out (circle generated-contract5))
         (contract-out (place-image generated-contract12))
         (contract-out (empty-scene generated-contract6))
         (contract-out (struct image ((impl g17)))))
