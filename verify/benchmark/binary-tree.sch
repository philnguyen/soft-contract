(module bt
  (provide
   [num (NODE/C . -> . number?)]
   [left (NODE/C . -> . BT/C)]
   [right (NODE/C . -> . BT/C)]
   [BT/C any/c]
   [NODE/C any/c])
  (define num car)
  (define (left node) (car (cdr node)))
  (define (right node) (cdr (cdr node)))
  (define BT/C (μ/c (X) (or/c number? (cons/c number? (cons/c X X)))))
  (define NODE/C (cons/c number? (cons/c BT/C BT/C))))

(module sum
  (provide [sum (BT/C . -> . number?)])
  (require bt)
  (define (sum t)
    (if (number? t) t
        (+ (num t) (+ (sum (left t)) (sum (right t)))))))

(module map
  (provide [map ((number? . -> . number?) BT/C . -> . BT/C)])
  (require bt)
  (define (map f t)
    (if (number? t) (f t)
        (cons (f (num t))
              (cons (map f (left t)) (map f (right t)))))))

(module t (provide [t BT/C]) (require bt))

(require sum map t)
(amb (sum t) (map add1 t))
