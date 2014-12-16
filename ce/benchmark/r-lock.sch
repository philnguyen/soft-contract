(module lock
  (provide [lock ((one-of/c 0) . -> . (one-of/c 1))]
           [unlock ((one-of/c 1) . -> . (one-of/c 0))])
  (define (lock st) 1)
  (define (unlock st) 0))

(module fg
  (provide [f (integer? integer? . -> . integer?)]
           [g (integer? integer? . -> . integer?)])
  (require lock)
  (define (f n st) (if (> n 0) (lock st) st))
  (define (g n st) (if (> n 0) (unlock st) st)))

(module main
  (provide [main (integer? . -> . (one-of/c 0))])
  (require fg)
  (define (main n) (g n (f n 0))))

(require main)
(main •)
