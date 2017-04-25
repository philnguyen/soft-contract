#lang racket

(require soft-contract/fake-contract)

(define church/c ((any/c . -> . any/c) . -> . (any/c . -> . any/c)))

(define (n->f n)
  (cond
    [(zero? n) (λ (f) (λ (x) x))]
    [else 
     (define n-1 (n->f (- n 1)))
     (λ (f) 
       (define fn-1 (n-1 f))
       (λ (x) (f (fn-1 x))))]))

(define (f->n c)
  ((c (λ (x) (+ x 1))) 0))

(define (c:* n1)
  (λ (n2) 
    (λ (f) 
      (n1 (n2 f)))))

(define (c:zero? c)
  ((c (λ (x) #f)) #t))

;; taken from Wikipedia (but lifted out
;; the definition of 'X')
(define (c:sub1 n)
  (λ (f) 
    (define X (λ (g) (λ (h) (h (g f)))))
    (λ (x) 
      (((n X) 
        (λ (u) x)) 
       (λ (u) u)))))

(define (c:! n)
  (cond
    [(c:zero? n) (λ (f) f)]
    [else ((c:* n) (c:! (c:sub1 n)))]))

(provide/contract
 [n->f (exact-nonnegative-integer? . -> . church/c)]
 [f->n (church/c . -> . exact-nonnegative-integer?)]
 [c:* (church/c . -> . (church/c . -> . church/c))]
 [c:zero? (church/c . -> . boolean?)]
 [c:sub1 (church/c . -> . church/c)]
 [c:! (church/c . -> . church/c)])
