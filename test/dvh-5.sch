; Demonstrates shortcoming in Phil's email from 7/13
; Weakened assume L1 * L1 = L3 and (not (zero? L3))
; verify: (not (zero? L1))
(module dvh-5
  (provide
   [phil  ([l1 : num?] . -> . 
	   ([l3 : (and/c num? 
			 (and/c (lambda (m) (not (zero? m)))
				(lambda (n) (= n (* l1 l1)))))] . -> . 
				(lambda (r) (not (zero? r)))))])

  (define phil
    (lambda (l1)
        (lambda (l3)
          l1))))

(require dvh-5)
((phil •) •)
