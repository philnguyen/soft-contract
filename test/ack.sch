(module ack
  (provide [ack ([_ : int?] [n : int?] . -> . (and/c int? (>/c n)))])
  (define (ack m n)
    (cond
      [(= m 0) (+ n 1)]
      [(= n 0) (ack (- m 1) 1)]
      [else (ack (- m 1) (ack m (- n 1)))])))

(require ack)
(ack • •)