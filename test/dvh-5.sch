; Demonstrates shortcoming in Phil's email from 7/13
; Weakened assume L1 * L1 = L3 and (not (zero? L3))
; verify: (not (zero? L1))
(module dvh-5
  (provide
   [phil ([l1 : num?] . -> . 
         ([l3 : (and/c num? (not/c zero?) (=/c (* l1 l1)))] . -> . (not/c zero?)))])

  (define phil
    (lambda (l1)
        (lambda (l3)
          l1))))

(require dvh-5)
((phil •) •)
