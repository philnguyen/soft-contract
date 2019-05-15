#lang racket

(define auto (λ _ 'trivial))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; fib (nat induction)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/contract plus-2-2
  (->i () (_ {} (λ (_) (= (+ 2 2) 4))))
  auto)
(define/contract plus-comm
  (->i ([x integer?]
        [y integer?])
       (_ {x y} (λ (_) (= (+ x y) (+ y x)))))
  auto)

(define/contract int-up
  (->i ([n integer?])
       (_ {n} (and/c integer? (λ (m) (< n m)))))
  (λ (n) (+ n 1)))

(define fib
  (match-lambda
    [0 0]
    [1 1]
    [n (+ (fib (- n 1)) (fib (- n 2)))]))

(define/contract fib-2=1
  (->i ()
       (_ {} (λ (_) (= (fib 2) 1))))
  (λ ()
    (fib 2) (fib 1) (fib 0)))

(define/contract fib-3=2
  (->i ()
       (_ {} (λ (_) (= (fib 3) 2))))
  (λ ()
    (fib 3) (fib 2) (fib 1) (fib-2=1)))

(define (up/c f)
  (->i ([n exact-nonnegative-integer?])
       (_ {n} (λ _ (<= (f n) (f (+ 1 n)))))))

(define/contract fib-up (up/c fib)
  (match-lambda
    [0 (<  (fib 0) (fib 1))]
    [1 (<= (fib 1) (+ (fib 1) (fib 0)))
       (= (fib 2) (+ (fib 1) (fib 0)))]
    [n (<= (fib n) (+ (fib n) (fib (- n 1))))
       (= (fib (+ n 1)) (+ (fib n) (fib (- n 1))))]))

(define mono/c
  (->i ([f (exact-nonnegative-integer? . -> . integer?)]
        [up {f} (up/c f)]
        [x exact-nonnegative-integer?]
        [y {x} (and/c exact-nonnegative-integer? (>/c x))])
       (_ {f x y} (λ (_) (<= (f x) (f y))))))

(define/contract f-mono mono/c
  (λ (f up x y)
    'TODO))

(define/contract fib-mono
  (->i ([n exact-nonnegative-integer?]
        [m {n} (and/c exact-nonnegative-integer? (>/c n))])
       (_ {n m} (λ (_) (<= (fib n) (fib m)))))
  (λ (n m)
    (f-mono fib fib-up n m)))

#;(provide
 (contract-out
  [plus-2-2 (->i () (_ {} (λ (_) (= (+ 2 2) 4))))]
  [plus-comm (->i ([x integer?]
                   [y integer?])
                  (_ {x y} (λ (_) (= (+ x y) (+ y x)))))]
  [int-up (->i ([n integer?])
               (_ {n} (and/c integer? (λ (m) (< n m)))))]
  [fib-2=1 (->i ()
                (_ {} (λ (_) (= (fib 2) 1))))]
  [fib-3=2 (->i ()
                (_ {} (λ (_) (= (fib 3) 2))))]
  [fib-up (up/c fib)]
  [f-mono mono/c]
  [fib-mono (->i ([n exact-nonnegative-integer?]
                  [m {n} (and/c exact-nonnegative-integer? (>/c n))])
                 (_ {n m} (λ (_) (<= (fib n) (fib m)))))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; append (list induction)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (append xs ys)
  (match xs
    ['() ys]
    [(cons x xs*) (cons x (append xs* ys))]))

(define (map f xs)
  (match xs
    ['() '()]
    [(cons x xs*) (cons (f x) (map f xs*))]))

(define append-nil-id/c
  (->i ([xs list?])
       (_ {xs} (λ (_) (equal? (append xs '()) xs)))))
(define append-assoc/c
  (->i ([xs list?]
        [ys list?]
        [zs list?])
       (_ {xs ys zs} (λ (_) (equal? (append xs (append ys zs))
                                    (append (append xs ys) zs))))))
(define map-fusion/c
  ;; FIXME parametric
  (->i ([f (any/c . -> . any/c)]
        [g (any/c . -> . any/c)]
        [xs list?])
       (_ {f g xs} (λ (_) (equal? (map (compose1 f g) xs)
                                  (map f (map g xs)))))))

(define/contract append-nil-id append-nil-id/c
  (match-lambda
    ['() 'trivial]
    [(cons _ xs) (append-nil-id xs)]))

(define/contract append-assoc append-assoc/c
  (λ (xs ys zs)
    (match xs
      ['() 'trivial]
      [(cons x xs*) (append-assoc xs* ys zs)])))

(define/contract map-fusion map-fusion/c
  (λ (f g xs)
    (match xs
      ['() 'trivial]
      [(cons x xs*)
       (map-fusion f g xs*)])))

#;(provide
 (contract-out
  [append-nil-id append-nil-id/c]
  [append-assoc append-assoc/c]
  [map-fusion map-fusion/c]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; swap (case analysis )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define swap
  (match-lambda
    [(list* x₁ x₂ xs) (if (> x₁ x₂) (list* x₂ x₁ xs) (list* x₁ x₂ xs))]
    [xs xs]))

(define/contract swap-idemp
  (->i ([xs (listof real?)])
       (_ {xs} (λ (_) (equal? (swap (swap xs)) xs))))
  (match-lambda
    [(list* x₁ x₂ xs) (if (> x₁ x₂) 'trivial 'trivial)]
    [_ 'trivial]))

#;(provide
 (contract-out
  [swap-idemp (->i ([xs (listof real?)])
                   (_ {xs} (λ (_) (equal? (swap (swap xs)) xs))))]))
