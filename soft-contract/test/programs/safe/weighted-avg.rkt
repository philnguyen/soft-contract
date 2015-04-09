#lang racket
(require soft-contract/fake-contract)

(define (weighted-avg x)
  (λ (w)
     (let* ([x@ (list@ x)]
	    [w@ (list@ w)]
	    [b (cons (* (x@ 0) (w@ 0)) (w@ 0))]
	    [f (λ (i s×n) (cons (+ (car s×n) (* (x@ i) (w@ i))) (+ (cdr s×n) (w@ i))))]
	    [sum×n ((foldn 1 (len x) b) f)])
       (/ (car sum×n) (cdr sum×n)))))

(define (foldn m n b)
  (λ (g) (if (< m n) ((foldn (+ m 1) n (g m b)) g) b)))

(define (list@ xs)
  (λ (i) (if (zero? i) (car xs) ((list@ (cdr xs)) (- i 1)))))

(define (len l) (if (empty? l) 0 (+ 1 (len (cdr l)))))

(provide/contract
 [weighted-avg (->i ([x (cons/c real? (listof real?))])
		    (res (x) ((and/c (cons/c (>/c 0) (listof (>/c 0))) (λ (w) (= (len x) (len w))))
			      . -> . real?)))])
