(abbrev/c BT/C (μ X (or/c num? (cons/c num? (cons/c X X)))))
(abbrev/c NODE/C (cons/c num? (cons/c BT/C BT/C)))

(module bt
  (provide
   [num (NODE/C . -> . num?)]
   [left (NODE/C . -> . BT/C)]
   [right (NODE/C . -> . BT/C)])
  (define num car)
  (define (left node) (car (cdr node)))
  (define (right node) (cdr (cdr node))))

(module sum
  (provide [sum (BT/C . -> . num?)])
  (require bt)
  (define (sum t)
    (if (num? t) t
        (+ (num t) (+ (sum (left t)) (sum (right t)))))))

(module map
  (provide [map ((num? . -> . num?) BT/C . -> . BT/C)])
  (require bt)
  (define (map f t)
    (if (num? t) (f t)
        (cons (f (num t))
              (cons (map f (left t)) (map f (right t)))))))

(module t (provide [t BT/C]))

(require sum map t)
(amb (sum t) (map add1 t))