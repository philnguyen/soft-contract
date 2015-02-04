(module f racket
  (provide/contract
   [f (#|HERE|# any/c cons? . -> . number?)])
  (define (f input extra)
    (cond
      [(and (number? input) (number? (car extra)))
       (+ input (car extra))]
      [(number? (car extra))
       (+ (string-length input) (car extra))]
      [else 0])))

(require 'f)
(f • •)
