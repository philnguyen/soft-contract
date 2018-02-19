#lang racket/base
(require racket/match
         racket/contract
         racket/list
         racket/function
         (only-in typed/racket/base assert)
         soft-contract/induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; fib (nat induction)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-theorem plus-2-2 (∀ () (= (+ 2 2) 4)))
(define-theorem plus-comm (∀ ([x y integer?]) (= (+ x y) (+ y x))))
(define-theorem int-up (->i ([n integer?]) (_ {n} (and/c integer? (λ (m) (< n m)))))
  #:proof (λ (n) (+ n 1)))

(define fib
  (match-lambda
    [0 0]
    [1 1]
    [n (+ (fib (- n 1)) (fib (- n 2)))]))

(define-theorem (fib-2=1) #:conclusion (= (fib 2) 1)
  #:proof
  (assert (= (fib 2) (+ (fib 1) (fib 0)))))

(define-theorem (fib-3=2) #:conclusion (= (fib 3) 2)
  #:proof
  (begin
    (assert (= (fib 3) (+ (fib 2) (fib 1))))
    ;; Somehow need to have kept around fib-2=1's flat contract
    ;; If execution never approximates, none of these is neccessary
    fib-2=1))

(define (up/c f)
  (->i ([n exact-nonnegative-integer?])
       (_ {n} (λ _ (<= (f n) (f (+ 1 n)))))))

(define-theorem fib-up (up/c fib)
  #:proof
  (match-lambda
    [0 (assert (<  (fib 0) (fib 1)))]
    [1 (assert (<= (fib 1) (+ (fib 1) (fib 0))))
       (assert (= (fib 2) (+ (fib 1) (fib 0))))]
    [n (assert (<= (fib n) (+ (fib n) (fib (- n 1)))))
       (assert (= (fib (+ n 1)) (+ (fib n) (fib (- n 1)))))]))

(define mono/c
  (∀ ([f (exact-nonnegative-integer? . -> . integer?)]
      [up (up/c f)]
      [x exact-nonnegative-integer?]
      [y (and/c exact-nonnegative-integer? (>/c x))])
     (<= (f x) (f y))))

(define-theorem f-mono mono/c
  #:proof
  (λ (f up x y)
    (nat-induct (- y (+ 1 x))
                (λ (d) (<= (f x) (f (+ x d))))
                (λ (d) (assert (<= (f x) (f (+ x 1)))))
                (λ (d ih)
                  (assert (<= (f x) (f (- y 1))))
                  (up (- y 1))))))

(define-theorem fib-mono
  (∀ ([n exact-nonnegative-integer?]
      [m (and/c exact-nonnegative-integer? (>/c n))])
     (<= (fib n) (fib m)))
  #:proof
  (λ (n m)
    (f-mono fib fib-up n m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; append (list induction)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; assume definitions of `append`, `map` available in same module

(define append-nil-id/c (∀ ([xs list?]) (equal? (append xs '()) xs)))
(define append-assoc/c
  (∀ ([xs ys zs list?]) (equal? (append xs (append ys zs)) (append (append xs ys) zs))))
(define map-fusion/c
  (∀/c {α β γ}
    (∀ ([f (β . -> . γ)] [g (α . -> . β)] [xs (listof α)])
      (equal? (map (compose1 f g) xs) (map f (map g xs))))))

(define-theorem append-nil-id append-nil-id/c
  #:proof
  (λ (xs)
    (list-induct xs
                 (λ (l) (λ _ (equal? (append l '()) l)))
                 trivial
                 trivial)))
(define-theorem append-assoc append-assoc/c
  #:proof
  (λ (xs ys zs)
    (list-induct
     xs
     (λ (l)
       (λ _ (equal? (append l (append ys zs))
                    (append (append l ys) zs))))
     (λ (_null) ; shouldn't need any of the blow
       (assert (equal? (append '() (append ys zs)) (append ys zs)))
       (assert (equal? (append (append '() ys) zs) (append ys zs))))
     (λ (x xs* ih) ; shouldn't need any/most of the below
       (define lhs  (append (cons x xs*) (append ys zs)))
       (define lhs* (cons x (append xs* (append ys zs))))
       (define rhs  (append (append (cons x xs*) ys) zs))
       (define rhs* (append (cons x (append xs* ys)) zs))
       (assert (equal? lhs lhs*))
       (assert (equal? rhs rhs*))
       (assert (equal? lhs* rhs*))))))
(define-theorem map-fusion map-fusion/c
  #:proof
  (λ (f g xs)
    (list-induct xs
                 (λ (l) (λ _ (equal? (map (compose1 f g) l) (map f (map g l)))))
                 trivial
                 trivial)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; swap (case analysis )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define swap
  (match-lambda
    [(list* x₁ x₂ xs) (if (> x₁ x₂) (list* x₂ x₁ xs) (list* x₁ x₂ xs))]
    [xs xs]))

(define-theorem swap-idemp
  (∀ ([xs list?]) (equal? (swap (swap xs)) xs))
  #:proof
  (match-lambda
    [(list* x₁ x₂ xs) (if (> x₁ x₂) 'duh 'duh)]
    [_ 'duh]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; extras
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/contract map-that-preserves-length
  (->i ([f (any/c . -> . any/c)]
        [xs list?])
       (_ {f xs} (and/c list? (λ (ys) (= (length ys) (length xs))))))
  (λ (f xs)
    #| Ignoring contracts, equivalent to:
    (foldr (λ (x ys) (cons (f x) ys))
           null
           xs)
    |#
    (list-induct xs
                 (λ (xs) (and/c list? (λ (ys) (= (length ys) (length xs)))))
                 (λ (_null) null)
                 (λ (x _xs* ys) (cons (f x) ys)))))

(define-theorem map-preserves-length
  (∀ ([f (any/c . -> . any/c)]
      [xs list?])
     (equal? (length (map f xs)) (length xs)))
  #:proof
  (λ (f xs)
    (list-induct xs
                 (λ (xs) (λ _ (equal? (length (map f xs)) (length xs))))
                 (λ (-null)
                   ; (assert (equal? (length (map f '())) (length '())))
                   'duh)
                 (λ (x xs* ih)
                   ; (assert (equal? (length (map f xs*)) (length xs*))) ; from `ih`
                   ; (assert (equal? (length (map f (cons x xs*))) (length (cons x xs*))))
                   'duh))))
