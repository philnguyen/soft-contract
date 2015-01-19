(module mc91 racket
  (provide/contract
   [mc91 (->i ([n integer?])
	      (res (n) (and/c integer? (λ (a) (implies #|HERE|#(< n 101) (= a 91))))))])
  (define (mc91 x)
    (if (> x 100) (- x 10)
        (mc91 (mc91 (+ x 11))))))

(require 'mc91)
(mc91 •)
