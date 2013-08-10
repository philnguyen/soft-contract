(module dvh-3
  (provide
   [  eq  ([x : num?] . -> . (=/c x))]
   [succ  ([x : num?] . -> . (=/c (add1 x)))]
   [succ2 ([x : num?] . -> . (lambda (z) (= x (sub1 z))))]
   [mult  ([x : num?] [y : num?] . -> . (=/c (* x y)))]
   ;; reverse order of mult in contract from implementation
   [mult2 ([x : num?] [y : num?] . -> . (=/c (* y x)))])

  (define (eq x) x)
  (define (succ x) (add1 x))
  (define (succ2 x) (add1 x))
  (define (mult x y) (* x y))
  (define (mult2 x y) (* x y)))

(require dvh-3)
(begin
 (eq •)
 (succ •)
 (succ2 •)

 (mult • •)  ;; BUG: these two expressions produce blame that is identified
 (mult2 • •) ;; so there's only one error report for the pair
 )