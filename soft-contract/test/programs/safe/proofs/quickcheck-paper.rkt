#lang racket

(define auto (λ _ 'trivial))

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

(define ordered?
  (match-lambda
    ['() #t]
    [(list _) #t]
    [(cons x₁ (and xs* (cons x₂ _))) (and (<= x₁ x₂) (ordered? xs*))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.1 Simple Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/contract thm-rev-unit
  (->i ([x any/c])
       (_ {x} (equal? (reverse (list x)) (list x))))
  auto)
(define/contract thm-rev-app
  (->i ([xs list?]
        [ys list?])
       (_ {xs ys} (λ (_) (equal? (reverse (append xs ys))
                                 (append (reverse ys) (reverse xs))))))
  (λ (xs ys)
    'TODO))
(define/contract thm-rev-rev
  (->i ([xs list?])
       (_ {xs} (λ (_) (equal? (reverse (reverse xs)) xs))))
  (λ (xs)
    'TODO))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.2 Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In paper, test needed a monomorphic instance.
;; Verification needs not.
(define ((=== f g) x) (equal? (f x) (g x)))
(define/contract thm-comp-assoc
  ;; FIXME parametric contract
  (->i ([f (any/c . -> . any/c)]
        [g (any/c . -> . any/c)]
        [h (any/c . -> . any/c)]
        [x any/c])
       (_ {f g h x} (λ (_) ((=== (compose1 f (compose1 g h)) (compose (compose1 f g) h)) x))))
  auto)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.3 Conditional Laws
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/contract thm-max-le
  (->i ([x integer?]
        [y {x} (and/c integer? (>=/c x))])
       (_ {x y} (λ (x y) (equal? (max x y) y))))
  auto)

(define/contract thm-insert
  (->i ([x integer?]
        [xs (and/c (listof integer?) ordered?)])
       (_ {x xs} (λ (_) (ordered? (insert x xs)))))
  auto)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.5 Infinite Structures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(TODO)

(provide
 (contract-out
  [thm-rev-unit (->i ([x any/c])
                     (_ {x} (equal? (reverse (list x)) (list x))))]
  [thm-rev-app (->i ([xs list?]
                     [ys list?])
                    (_ {xs ys} (λ (_) (equal? (reverse (append xs ys))
                                              (append (reverse ys) (reverse xs))))))]
  [thm-rev-rev (->i ([xs list?])
                    (_ {xs} (λ (_) (equal? (reverse (reverse xs)) xs))))]
  [thm-comp-assoc
   ;; FIXME parametric contract
   (->i ([f (any/c . -> . any/c)]
         [g (any/c . -> . any/c)]
         [h (any/c . -> . any/c)]
         [x any/c])
        (_ {f g h x} (λ (_) ((=== (compose1 f (compose1 g h)) (compose (compose1 f g) h)) x))))]
  [thm-max-le (->i ([x integer?]
                    [y {x} (and/c integer? (>=/c x))])
                   (_ {x y} (λ (x y) (equal? (max x y) y))))]
  [thm-insert (->i ([x integer?]
                    [xs (and/c (listof integer?) ordered?)])
                   (_ {x xs} (λ (_) (ordered? (insert x xs)))))]))
