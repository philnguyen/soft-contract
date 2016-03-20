; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/sat.sch
#lang racket

(require soft-contract/fake-contract)

(define phi
  (λ (x1)
    (λ (x2)
      (λ (x3)
        (λ (x4)
          (λ (x5)
            (λ (x6)
              (λ (x7)
                (and (or x1 x2)
                     (or x1 (not x2) (not x3))
                     (or x3 x4)
                     (or (not x4) x1)
                     (or (not x2) (not x3))
                     (or x4 x2))))))))))

(define try
  (λ (f) (or (f #t) (f #f))))

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

(sat-solve-7 phi)
