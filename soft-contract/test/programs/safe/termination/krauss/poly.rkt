#lang racket/base

(require racket/match
         soft-contract/fake-contract)

(struct Pc (c) #:transparent)
(struct Pinj (i P) #:transparent)
(struct PX (P i Q) #:transparent)
(define mkPX #|is it?|# PX)
(define mkPinj #|is it?|# Pinj)
(define P/c (or/c (struct/c Pc exact-nonnegative-integer?)
                  (struct/c Pinj exact-nonnegative-integer? (recursive-contract P/c #:flat))
                  (struct/c PX
                            (recursive-contract P/c #:flat)
                            exact-nonnegative-integer?
                            (recursive-contract P/c #:flat))))
(define add
  (match-lambda**
   [((Pc a) (Pc b)) (Pc (+ a b))]
   [((Pc c) (Pinj i P)) (Pinj i (add P (Pc c)))]
   [((Pc c) (PX P i Q)) (PX P i (add Q (Pc c)))]
   [((Pinj x P) (Pinj y Q))
    (cond [(= x y) (mkPinj x (add P Q))]
          [(< y x) (mkPinj y (add (Pinj (- x y) P) Q))]
          [else #|permute|# (add (Pinj y Q) (Pinj x P))])]
   [((Pinj x P) (PX Q y R))
    (case x
      [(0)  (add P (PX Q y R))]
      [(1)  (PX Q y (add P R))]
      [else (PX Q y (add (Pinj (- x 1) P) R))])]
   [((PX P₁ x P₂) (PX Q₁ y Q₂))
    (cond [(= x y) (mkPX (add P₁ Q₁) x (add P₂ Q₂))]
          [(< y x) (mkPX (add (PX P₁ (- x y) (Pc 0)) Q₁)
                         y
                         (add P₂ Q₂))]
          [else #|permute|# (add (PX Q₁ y Q₂) (PX P₁ x P₂))])]
   [((Pinj i P) (Pc c)) #|permute|# (add (Pc c) (Pinj i P))]
   [((PX P i Q) (Pc c)) #|permute|# (add (Pc c) (PX P i Q))]
   [((PX Q y R) (Pinj x P)) #|permute|# (add (Pinj x P) (PX Q y R))]))

(define (run)
  (add (Pinj 42 (Pc 0)) (Pc 42)))

(provide
 (contract-out
  [run (-> any/c #:total? #t)]
  #;[add (P/c P/c . -> . P/c #:total? #t)]))
