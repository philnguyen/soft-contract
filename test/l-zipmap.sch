(module zip
  (provide [zip (int? int? . -> . int?)])
  (define (zip x y)
    (cond
      [(and (zero? x) (zero? y)) x]
      [(and (positive? x) (positive? y)) (+ 1 (zip (- x 1) (- y 1)))]
      [else 'fail])))

(module map
  (provide [map (int? . -> . int?)])
  (define (map x)
    (if (zero? x) x (+ 1 (map (- x 1))))))

(module main
  (provide [main ([n : int?] . -> . (and/c int? (=/c n)))])
  (require zip map)
  (define (main n) (map (zip n n))))

(require main)
(main •)