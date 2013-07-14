; Demonstrates shortcoming in Phil's email from 7/13
(module dvh-4
  (provide
   [phil  ([l1 : num?] . -> . 
           ([l2 : num?] . -> .
            ([l3 : (and/c num? 
			  (and/c (lambda (m) (not (zero? m)))
				 (lambda (n) (= n (* l1 l2)))))] . -> . 
				 (lambda (r) (not (zero? r))))))])

  (define phil
    (lambda (l1)
      (lambda (l2)
        (lambda (l3)
          l1)))))

(require dvh-4)
(((phil •) •) •)
