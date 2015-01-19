(module m racket
  (provide
   (contract-out
    [assert-1 (-> (not/c false?))]
    [assert-2 (-> (not/c false?))]
    [assert-3 (-> (not/c false?))]
    [assert-4 (number? number? . -> . (not/c false?))]
    [assert-5 (real? real? . -> . (not/c false?))]))
  (define (assert-1)
    (= (expt 2 3) 8))
  (define (assert-2)
    (= (expt 4 0.5) 2.0))
  (define (assert-3)
    (= (expt +inf.0 0) 1))
  (define (assert-4 z w)
    (implies (= w 0)
             (= 1 (expt z w))))
  (define (assert-5 z w)
    (implies (= z 1)
             (= 1 (expt z 1)))))
