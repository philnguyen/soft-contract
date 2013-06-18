(module lastpair
  (provide
   [lastpair (cons? . -> . cons?)])
  (define (lastpair x)
    (if (cons? (cdr x)) (lastpair (cdr x)) x)))

(require lastpair)
(lastpair (cons • •))