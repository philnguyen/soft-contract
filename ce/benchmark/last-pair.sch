(module lastpair racket
  (provide/contract
   [lastpair (cons? . -> . cons?)])
  (define (lastpair x)
    (if (cons? #|HERE|# x) (lastpair (cdr x)) x)))

(require 'lastpair)
(lastpair (cons • •))
