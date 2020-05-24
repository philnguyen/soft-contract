#lang racket/base

(require racket/contract
         racket/match
         soft-contract/induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (append xs ys)
  (match xs
    ['() ys]
    [(cons x xs*) (cons x (append xs* ys))]))

(define (reverse xs)
  (match xs
    ['() '()]
    [(cons x xs*) (append (reverse xs*) (list x))]))

(define (insert x xs)
  (match xs
    ['() (list x)]
    [(cons x* xs*) (cond [(<= x x*) (list* x x* xs*)]
                         [else (cons x* (insert x xs*))])]))

(define (ordered? xs)
  (match xs
    ['() #t]
    [(list _) #t]
    [(cons x₁ (and xs* (cons x₂ _))) (and (<= x₁ x₂) (ordered? xs*))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.1 Simple Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-theorem thm-rev-unit (∀ (x) (equal? (reverse (list x)) (list x))))
(define-theorem thm-rev-app (∀ ([xs ys list?]) (equal? (reverse (append xs ys)) (append (reverse ys) (reverse xs)))))
(define-theorem thm-rev-rev (∀ ([xs list?]) (equal? (reverse (reverse xs)) xs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.2 Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In paper, test needed a monomorphic instance.
;; Verification needs not.
(define ((=== f g) x) (equal? (f x) (g x)))
(define-theorem thm-comp-assoc
  (∀/c (α β γ δ)
    (∀ ([f (γ . -> . δ)] [g (β . -> . γ)] [h (α . -> . β)] [x α])
      ((=== (compose1 f (compose1 g h)) (compose (compose1 f g) h)) x))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.3 Conditional Laws
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-theorem thm-max-le
  (∀ ([x integer?] [y (and/c integer? (>=/c x))])
     (equal? (max x y) y)))

(define-theorem thm-insert
  (∀ ([x integer?] [xs (and/c (listof integer?) ordered?)])
    (ordered? (insert x xs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.5 Inifite Structures (TODO)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
