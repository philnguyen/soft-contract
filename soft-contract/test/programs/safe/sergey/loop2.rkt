; https://github.com/dvanhorn/oaam/blob/master/benchmarks/sergey/loop2.sch
#lang racket

(require soft-contract/fake-contract)

(let ([lp1 2000])
  (let ([a
         (set! lp1 (λ (i x)
                     (let ([a (= 0 i)])
                       (if
                        a
                        x
                        (let ([lp2 1000]) ;; FIXME should '(unspecified)
                          (let ([b
                                 (set! lp2 (λ (j f y)
                                             (let ([b (= 0 j)])
                                               (if b
                                                   (lp1 (- i 1) y)
                                                   (let ([$tmp$3 (f y)])
                                                     (lp2 (- j 1) f $tmp$3))))))])
                            (lp2 10 (λ (n) (+ n i )) x)))))))])
    (lp1 10 0)))
