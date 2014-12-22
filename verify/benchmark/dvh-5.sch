; Demonstrates shortcoming in Phil's email from 7/13
; Weakened assume L1 * L1 = L3 and (not (zero? L3))
; verify: (not (zero? L1))
(module dvh-5 racket
  (provide/contract
   [phil (->i ([l1 number?])
	      (res (l1)
		   (->i ([l3 (and/c number? (not/c zero?) (=/c (* l1 l1)))]) (res (l3) (not/c zero?)))))])

  (define phil
    (lambda (l1)
        (lambda (l3)
          l1))))

(require 'dvh-5)
((phil •) •)
