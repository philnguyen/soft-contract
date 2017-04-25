#lang racket

(require soft-contract/fake-contract)

(define try
  (λ (f) (or (f #f) (f #t))))

(define sat-solve-7
  (λ (p)
    (try (λ (n1)
           (try (λ (n2)
                  (try (λ (n3)
                         (try (λ (n4)
                                (try (λ (n5)
                                       (try (λ (n6)
                                              (try (λ (n7)
                                                     (((((((p n1) n2) n3) n4) n5) n6) n7)))))))))))))))))
(define phi
  (λ (x1)
    (λ (x2)
      (λ (x3)
        (λ (x4)
          (λ (x5)
            (λ (x6)
              (λ (x7)
                (and x1 x2 x3 x4 x5 x6 x7)))))))))

(define psi
  (λ (x1)
    (λ (x2)
      (λ (x3)
        (λ (x4)
          (λ (x5)
            (λ (x6)
              (λ (x7)
                (and x7 (not x7))))))))))

(provide
 (contract-out
  [sat-solve-7 any/c]))

(values (sat-solve-7 phi) (sat-solve-7 psi))
