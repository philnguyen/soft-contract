(module zip
  (provide [zip (integer? integer? . -> . integer?)])
  (define (zip x y)
    (cond
      [(and (= x 0) (= y 0)) x]
      [(and (not (= x 0)) (not (= y 0))) (+ 1 (zip (- x 1) (- y 1)))]
      [else 'fail])))

(module map
  (provide [map (integer? . -> . integer?)])
  (define (map x)
    (if (= x 0) x (+ 1 (map (- x 1))))))

(module main
  (provide [main (->i ([n integer?]) (res (n) (and/c integer? (=/c n))))])
  (require zip map)
  (define (main n) (map (zip n n))))

(require main)
(main •)
