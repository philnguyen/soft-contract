(module dvh-3
  (provide
   [  eq ([x : num?] . -> . (lambda (z) (= x z)))]
   [succ ([x : num?] . -> . (lambda (z) (= (add1 x) z)))]
   [mult ([x : num?] [y : num?] . -> . (lambda (z) (= (* x y) z)))]
   ;; reverse order of mult in contract from implementation
   [mult2 ([x : num?] [y : num?] . -> . (lambda (z) (= (* y x) z)))])

  (define (eq x) x)
  (define (succ x) (add1 x))
  (define (mult x y) (* x y))
  (define (mult2 x y) (* x y)))

(require dvh-3)
(begin
 (eq •)
 (succ •)

 (mult • •)  ;; BUG: these two expressions produce blame that is identified
 (mult2 • •) ;; so there's only one error report for the pair
 )