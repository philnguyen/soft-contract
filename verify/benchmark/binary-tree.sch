(module bt racket
  (provide/contract
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

(module sum racket
  (provide/contract [sum (BT/C . -> . number?)])
  (require (submod ".." bt))
  (define (sum t)
    (if (number? t) t
        (+ (num t) (+ (sum (left t)) (sum (right t)))))))

(module map racket
  (provide/contract [map ((number? . -> . number?) BT/C . -> . BT/C)])
  (require (submod ".." bt))
  (define (map f t)
    (if (number? t) (f t)
        (cons (f (num t))
              (cons (map f (left t)) (map f (right t)))))))

(module t racket
  (provide/contract [t BT/C]) (require (submod ".." bt)))

(require 'sum 'map 't)
(amb (sum t) (map add1 t))
