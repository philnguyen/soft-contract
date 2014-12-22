(module negate racket
  (provide/contract [negate ((or/c integer? boolean?) . -> . (or/c integer? boolean?))])
  (define (negate x)
    (if (integer? x) (- 0 x) (not x))))

(module maybe-apply racket
  (provide/contract [maybe-apply (integer? (or/c false? (integer? . -> . integer?)) . -> . integer?)])
  (define (maybe-apply x f)
    (if (false? f) x (f x))))

(module opaque racket (provide/contract [n integer?]))

(module main racket
  (provide/contract [main (-> integer?)])
  (require (submod ".." maybe-apply) (submod ".." negate) (submod ".." opaque))
  (define (main)
    (maybe-apply n negate)))

(require 'negate 'maybe-apply 'main)
(amb (negate •) (maybe-apply • •) (main))
