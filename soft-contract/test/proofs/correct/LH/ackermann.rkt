#lang racket/base

(require racket/match
         racket/contract
         soft-contract/induction)

;; Source:
;; https://github.com/ucsd-progsys/liquidhaskell/blob/develop/benchmarks/popl18/ple/pos/Ackermann.hs

(define ack
  (match-lambda**
   [(0 x) (+ x 2)]
   [(n 0) 2]
   [(n x) (ack (- n 1) (ack n (- x 1)))]))

(define (iack h n x)
  (case h
    [(0)  x]
    [else (ack n (iack (- h 1) n x))]))

(define-theorem (def-eq [n x exact-nonnegative-integer?])
  #:conclusion (= (ack (+ n 1) x) (iack x n 2))
  #:proof
  (trivial-nat-induct x (λ (x) (↑ (= (ack (+ n 1) x) (iack x n 2))))))

(define-theorem lemma-2 ; TODO decrease in both `n` and `x`
  (∀ ([n x exact-nonnegative-integer?]) (< (+ x 1) (ack n x))))

(define-theorem lemma-3 ; TODO decrease in both `n` and `x`
  (∀ ([n x exact-nonnegative-integer?]) (< (ack n x) (ack n (+ x 1)))))

(define-theorem lemma-3-gen ; TODO
  (∀ ([n x exact-nonnegative-integer?]
      [y (and/c exact-nonnegative-integer? (>/c x))])
     (< (ack n x) (ack n y))))

(define-theorem (lemma-3-eq [n x exact-nonnegative-integer?]
                            [y (and/c exact-nonnegative-integer? (>=/c x))])
  #:conclusion (<= (ack n x) (ack n y))
  #:proof
  (trivial-nat-induct (- y x) (λ (d) (↑ (<= (ack n x) (ack n y))))))

(define-theorem (lemma-4 [x exact-positive-integer?]
                         [n exact-nonnegative-integer?])
  #:conclusion (< (ack n x) (ack (+ n 1) x))
  #:proof
  (begin (lemma-2 (+ n 1) (- x 1))
         (lemma-3-gen n x (ack (+ n 1) (- x 1)))))

(define-theorem lemma-4-gen
  (∀ ([n exact-nonnegative-integer?]
      [m (and/c exact-nonnegative-integer? (>/c n))]
      [x exact-positive-integer?])
     (< (ack n x) (ack m x))))

(define-theorem (lemma-4-eq [n x exact-nonnegative-integer?])
  #:conclusion (<= (ack n x) (ack (+ n 1) x))
  #:proof
  (case x
    [(0) 'duh]
    [else (lemma-4 x n)]))

(define-theorem (lemma-5 [h n x exact-nonnegative-integer?])
  #:conclusion (< (iack h n x) (iack (+ h 1) n x))
  #:proof (lemma-2 n (iack h n x)))

(define-theorem (lemma-6 [h n x exact-nonnegative-integer?])
  #:conclusion (< (iack h n x) (iack h n (+ x 1)))
  #:proof
  (nat-induct x
              (λ (x) (↑ (< (iack h n x) (iack h n (+ x 1)))))
              trivial
              (λ (x* x*.IH)
                (lemma-3-gen n (iack (- h 1) n x) (iack (- h 1) n (+ x 1))))))

(define-theorem (lemma-6-gen [h n x exact-nonnegative-integer?]
                             [y (and/c exact-nonnegative-integer? (>/c x))])
  #:conclusion (< (iack h n x) (iack h n y)))

(define-theorem (lemma-7-gen [h n x exact-nonnegative-integer?])
  #:conclusion (< (iack h n x) (iack h (+ n 1) x))
  #:proof
  (nat-induct h
              (λ (h) (↑ (< (iack h n x) (iack h (+ n 1) x))))
              trivial
              (λ (h* h*.IH)
                (lemma-4-eq n (iack (- h 1) n x))
                (lemma-3-eq (+ n 1) (iack (- h 1) n x) (iack (- h 1) (+ n 1) x)))))

(define-theorem (lemma-9 [n exact-positive-integer?]
                         [x exact-nonnegative-integer?]
                         [l (and/c exact-integer? (</c (+ x 2)))])
  #:conclusion (< (+ x 1) (ack n x))) ; TODO

(define-theorem (lemma-9-helper [x exact-nonnegative-integer?]
                                [l (and/c exact-integer? (</c (+ x 2)))])
  #:conclusion (< (+ x 1) (ack 1 x))) ; TODO

(define-theorem (lemma-10 [n exact-nonnegative-integer?]
                          [x exact-positive-integer?]
                          [l (and/c exact-nonnegative-integer? (</c x))])
  #:conclusion (< (iack l n x) (ack (+ n 1) x)))

(define-theorem (lemma-10-zero [l x exact-nonnegative-integer?])
  #:conclusion (= (iack l 0 x) (* (+ x 2) l))
  #:proof (nat-induct l
                      (λ (l) (↑ (= (iack l 0 x) (* (+ x 2) l))))
                      (λ (l₀) (assert (= (iack 0 0 x) x)))
                      trivial))

(define-theorem (lemma-10-one [x exact-nonnegative-integer?])
  #:conclusion (= (ack 1 x) (+ 2 (* 2 x)))
  #:proof (nat-induct x
                      (λ (x) (↑ (= (ack 1 x) (+ 2 (* 2 x)))))
                      (λ (x₀) (assert (= (ack 1 0) 2)))
                      trivial))

(define-theorem (lemma-10-helper [n exact-nonnegative-integer?]
                                 [x exact-positive-integer?]
                                 [l (and/c exact-nonnegative-integer?
                                           (λ (l) (< (* 2 l) x))
                                           (<=/c x))])
  #:conclusion (< x (iack (- x 1) n 2))
  #:proof (begin (def-eq n (- x 1))
                 (lemma-9 (+ n 1) (- x 1) l)))

(define/contract ladder
  (exact-nonnegative-integer? exact-positive-integer? exact-nonnegative-integer?
                              . -> . exact-nonnegative-integer?)
  (match-lambda**
   [(0 _ b) b]
   [(l n b) (iack (ladder (- l 1) n b) (- n 1) 2)]))

(define-theorem (ladder-prop-1 [n exact-positive-integer?]
                               [l x exact-nonnegative-integer?])
  #:conclusion (= (iack l n x) (ladder l n x))
  #:proof (nat-induct l
                      (λ (l) (↑ (= (iack l n x) (ladder l n x))))
                      trivial
                      (λ (l* l*.IH)
                        (def-eq (- n 1) (ladder (- l 1) n x)))))

(define-theorem (ladder-prop-2 [x y exact-nonnegative-integer?]
                               [n exact-positive-integer?]
                               [z exact-nonnegative-integer?])
  #:conclusion (= (ladder (+ x y) n z) (ladder x n (ladder y n z)))
  #:proof
  (trivial-nat-induct
   x
   (λ (x) (↑ (= (ladder (+ x y) n z) (ladder x n (ladder y n z)))))))

(define-theorem (ladder-prop-3 [x exact-nonnegative-integer?]
                               [y (and/c exact-nonnegative-integer? (>/c x))]
                               [n exact-positive-integer?]
                               [l exact-nonnegative-integer?])
  #:conclusion (< (ladder l n x) (ladder l n y))
  #:proof (begin (ladder-prop-1 n l x)
                 (ladder-prop-1 n l y)
                 (lemma-6-gen l n x y)))

(define-theorem (lemma-11 [n x y exact-nonnegative-integer?])
  #:conclusion (< (iack x n y) (ack (+ n 1) (+ x y)))
  #:proof (begin (def-eq n (+ x y))
                 (lemma-11-helper n x y 2)
                 (def-eq n y)
                 (lemma-2 (+ n 1) y)
                 (lemma-6-gen x n y (ack (+ n 1) y))))

(define-theorem (lemma-11-helper [n x y z exact-nonnegative-integer?])
  #:conclusion (= (iack (+ x y) n z) (iack x n (iack y n z)))
  #:proof
  (trivial-nat-induct
   x
   (λ (x) (↑ (= (iack (+ x y) n z) (iack x n (iack y n z)))))))

