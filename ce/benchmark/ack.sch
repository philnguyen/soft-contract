(module ack ; weakening the 1st arg will make program loop (never wrong)
  (provide [ack (integer? #|HERE|#real? . -> . integer?)])
  (define (ack m n)
    (cond
      [(= m 0) (+ n 1)]
      [(= n 0) (ack (- m 1) 1)]
      [else (ack (- m 1) (ack m (- n 1)))])))

(require ack)
(ack • •)
