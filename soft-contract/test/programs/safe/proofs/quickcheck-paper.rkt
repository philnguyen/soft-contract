#lang racket

(require soft-contract/fake-contract)

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
;;;;; helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define prop:append-right-id
  (->i ([l list?])
       (_ {l} (λ (_) (equal? (append l '()) l)))
       #:total? #t))
(define/contract append-right-id
  prop:append-right-id
  (match-lambda
    ['() 'trivial]
    [(cons _ l) (append-right-id l)]))

(define prop:append-assoc
  (->i ([xs list?]
        [ys list?]
        [zs list?])
       (_ {xs ys zs} (λ (_) (equal? (append (append xs ys) zs)
                                    (append xs (append ys zs)))))
       #:total? #t))
(define/contract append-assoc
  prop:append-assoc
  (λ (xs ys zs)
    (match xs
      ['() 'trivial]
      [(cons _ xs*) (append-assoc xs* ys zs)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.1 Simple Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prop:rev-unit
  (->i ([x any/c])
       (_ {x} (λ (_) (equal? (reverse (list x)) (list x))))
       #:total? #t))
(define/contract proof:rev-unit
  prop:rev-unit
  auto)

(define prop:rev-app
  (->i ([Xs list?]
        [Ys list?])
       (_ {Xs Ys} (λ (_) (equal? (reverse (append Ys Xs))
                                 (append (reverse Xs) (reverse Ys)))))
       #:total? #t))
(define/contract proof:rev-app
  prop:rev-app
  (λ (Xs Ys)
    (match Ys
      ['() (append-right-id (reverse Xs))]
      [(cons Y Ys*) (proof:rev-app Xs Ys*)
                    (append-assoc (reverse Xs) (reverse Ys*) (list Y))])))

(define prop:rev-rev
  (->i ([xs list?])
       (_ {xs} (λ (_) (equal? (reverse (reverse xs)) xs)))
       #:total? #t))
(define/contract proof:rev-rev
  prop:rev-rev
  (match-lambda
    ['() 'trivial]
    [(cons x xs*) (proof:rev-rev xs*)
                  (proof:rev-unit x)
                  (proof:rev-app (list x) (reverse xs*))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.2 Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In paper, test needed a monomorphic instance.
;; Verification needs not.
#;(define ((=== f g) x) (equal? (f x) (g x)))
#;(define ((compose f g) x) (f (g x)))
#;(define/contract proof:comp-assoc
  ;; FIXME parametric contract
  (->i ([f (any/c . -> . any/c)]
        [g (any/c . -> . any/c)]
        [h (any/c . -> . any/c)]
        [x any/c])
       (_ {f g h x} (λ (_) ((=== (compose f (compose g h)) (compose (compose f g) h)) x))))
  auto)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.3 Conditional Laws
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;(define/contract proof:max-le
  (->i ([x integer?]
        [y {x} (and/c integer? (>=/c x))])
       (_ {x y} (λ (x y) (equal? (max x y) y))))
  auto)

(define prop:insert
  (->i ([x integer?]
        [xs (listof integer?)])
       (_ {x xs} (λ (_)
                   (if (ordered? xs)
                       (ordered? (insert x xs))
                       #t)))
       #:total? #t))
(define/contract proof:insert
  prop:insert
  (λ (x xs)
    'TODO))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.5 Infinite Structures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(TODO)

(provide
 (contract-out
  [proof:rev-unit prop:rev-unit]
  [proof:rev-app prop:rev-app]
  [proof:rev-rev prop:rev-rev]
  #;[proof:comp-assoc
   ;; FIXME parametric contract
     prop:comp-assoc]
  #;[proof:max-le prop:max-le]
  #;[proof:insert prop:insert]))
