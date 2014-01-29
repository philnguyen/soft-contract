(module bubblesort
  (provide
   [sorted? ((listof int?) . -> . bool?)]
   [bsorthelper ((listof int?) . -> . (and/c (cons/c (listof int?) bool?)
                                             (λ (r)
                                               (implies (not (cdr r)) (sorted? (car r))))))]
   [bubblesort ((listof int?) . -> . (and/c (listof int?) sorted?))])
  (define (bubblesort xs)
    (let* ([ans (bsorthelper xs)]
           [result (car ans)])
      (if (cdr ans) (bubblesort result) result)))
  (define (bsorthelper xs)
    (cond
      [(empty? xs) (cons empty #f)]
      [(empty? (cdr xs)) (cons xs #f)]
      [else (let ([x (car xs)]
                  [xs (cdr xs)])
              (let* ([ans (bsorthelper xs)]
                     [result (car ans)]
                     [changed? (cdr ans)]
                     [y (car result)]
                     [ys (cdr result)])
                (if (<= x y) (cons (cons x (cons y ys)) changed?)
                    (cons (cons y (cons x ys)) #t))))]))
  (define (sorted? xs)
    (cond
      [(empty? xs) #t]
      [(empty? (cdr xs)) #t]
      [else (let* ([x (car xs)]
                   [xs (cdr xs)]
                   [y (car xs)])
              (and (<= x y) (sorted? xs)))])))

(require bubblesort)

(• sorted?)